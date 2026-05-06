/**
 * @license
 * SPDX-License-Identifier: Apache-2.0
 */

import { useEffect, useRef, useState, useCallback } from 'react';
import { initializeApp } from 'firebase/app';
import { getAuth, signInAnonymously, onAuthStateChanged, User } from 'firebase/auth';
import { getFirestore, collection, addDoc, serverTimestamp, query, orderBy, limit, onSnapshot, doc, setDoc } from 'firebase/firestore';
import firebaseConfig from '../firebase-applet-config.json';

// Initialize Firebase
const app = initializeApp(firebaseConfig);
const db = getFirestore(app);
const auth = getAuth(app);

function resamplePath(path: { x: number, y: number, r: number, strokeId: number }[], spacing = 4) {
  const newPath: { x: number, y: number, r: number, strokeId: number }[] = [];
  if (path.length < 2) return path;
  for (let i = 1; i < path.length; i++) {
    const p0 = path[i - 1];
    const p1 = path[i];
    
    // Se forem de traços diferentes, não interpola entre eles
    if (p0.strokeId !== p1.strokeId) {
      newPath.push(p0);
      continue;
    }

    const dx = p1.x - p0.x;
    const dy = p1.y - p0.y;
    const dr = p1.r - p0.r;
    const dist = Math.hypot(dx, dy);
    const steps = Math.max(1, Math.floor(dist / spacing));

    for (let j = 0; j < steps; j++) {
      const t = j / steps;
      newPath.push({
        x: p0.x + dx * t,
        y: p0.y + dy * t,
        r: p0.r + dr * t,
        strokeId: p0.strokeId
      });
    }
  }
  // Adiciona o último ponto
  newPath.push(path[path.length - 1]);
  return newPath;
}

function distanceToPath(px: number, py: number, path: { x: number, y: number, r: number, strokeId: number }[]) {
  let min = Infinity;
  let index = 0;
  let radius = 0;

  for (let i = 0; i < path.length; i++) {
    const dx = px - path[i].x;
    const dy = py - path[i].y;
    const d = Math.sqrt(dx * dx + dy * dy) - (path[i].r || 10);

    if (d < min) {
      min = d;
      index = i;
      radius = path[i].r || 10;
    }
  }

  return { dist: min, index, radius };
}

const PARTICLE_COUNT = 12000;
const GRID_RES = 7;
const CYCLE_TIME = 10000;
const DRAW_TIME = 7500;

const VIRTUAL_WIDTH = 720;
const VIRTUAL_HEIGHT = 1280;

const V_SHADER_SOURCE = `
    attribute vec2 a_position;
    varying vec2 v_uv;
    void main() {
        v_uv = a_position * 0.5 + 0.5;
        v_uv.y = 1.0 - v_uv.y;
        gl_Position = vec4(a_position, 0.0, 1.0);
    }
`;

const F_SHADER_SOURCE = `
    precision highp float;
    varying vec2 v_uv;
    uniform sampler2D u_tex;
    uniform sampler2D u_energy;
    uniform float u_time;
    uniform float u_fixFactor;

    void main() {
        vec2 uv = v_uv;
        float energy = texture2D(u_energy, uv).r;
        
        // Efeito Lente Buraco Negro / Bold
        // Distorce o UV em direção ao centro da energia
        vec2 center = vec2(0.5, 0.5);
        vec2 toCenter = uv - center;
        float distToCenter = length(toCenter);
        
        // A distorção de lente aumenta com a energia e o fator de fixação
        float lensStrength = energy * u_fixFactor * 0.15;
        vec2 lensUV = uv - normalize(toCenter) * lensStrength * (1.0 - distToCenter);
        
        float eLeft = texture2D(u_energy, lensUV - vec2(0.012, 0.0)).r;
        float eTop = texture2D(u_energy, lensUV - vec2(0.0, 0.012)).r;
        
        vec2 distortion = vec2(energy - eLeft, energy - eTop) * (0.35 + u_fixFactor * 0.4);
        
        vec2 finalUV = lensUV + distortion;
        
        float r = texture2D(u_tex, finalUV + distortion * 0.4).r;
        float g = texture2D(u_tex, finalUV).g;
        float b = texture2D(u_tex, finalUV - distortion * 0.4).b;
        
        gl_FragColor = vec4(r, g, b, 1.0);
    }
`;

class Particle {
  x: number = 0;
  y: number = 0;
  px: number = 0;
  py: number = 0;
  z: number = 0;
  vx: number = 0;
  vy: number = 0;
  accelX: number = 0;
  accelY: number = 0;
  energy: number = 0;
  memoryEnergy: number = 0;
  baseColor: string = '';
  color: string = '';
  hasPath: boolean = false;
  friction: number = 0;
  noiseScale: number = 0;
  offset: number = 0;
  targetIndex: number = 0;
  ease: number = 0;
  angleOffset: number = 0;

  constructor(width: number, height: number) {
    this.reset(width, height);
  }

  reset(width: number, height: number) {
    this.x = this.px = Math.random() * width;
    this.y = this.py = Math.random() * height;
    this.z = Math.random();
    this.vx = 0;
    this.vy = 0;
    this.accelX = 0;
    this.accelY = 0;
    this.energy = 0;
    this.memoryEnergy = 0;

    const palettes = ['#4285f4', '#ea4335', '#fbbc05', '#34a853'];
    this.baseColor = palettes[Math.floor(Math.random() * palettes.length)];
    this.color = this.baseColor;
    this.hasPath = false;
    this.friction = 0.9 + (this.z * 0.04);
    this.noiseScale = 0.0003 + (Math.random() * 0.0005);
    this.offset = Math.random() * 100;
  }

  update(width: number, height: number, phase: 'DRAW' | 'FIX', grid: any[][], memoryGrid: any[][], mousePos: { x: number, y: number }, lastMousePos: { x: number, y: number }, isMouseDown: boolean, resampledPath: { x: number, y: number, r: number, strokeId: number }[] | null, elapsed: number, viewMode: 'studio' | 'artifact') {
    this.px = this.x;
    this.py = this.y;

    const now = Date.now();
    const t = now * 0.0003;
    const depthSpeed = (1.0 - this.z * 0.5);

    // MOVIMENTO BASE
    const noiseX = Math.sin(this.y * this.noiseScale + t + this.offset) * (0.12 * depthSpeed);
    const noiseY = Math.cos(this.x * this.noiseScale + t + this.offset) * (0.12 * depthSpeed);

    this.vx += noiseX + this.accelX;
    this.vy += noiseY + this.accelY;

    const gx = Math.floor(this.x / GRID_RES);
    const gy = Math.floor(this.y / GRID_RES);
    
    // Leitura dos campos
    if (grid[gx] && grid[gx][gy]) {
      this.energy = grid[gx][gy].energy;
      this.memoryEnergy = memoryGrid[gx]?.[gy]?.energy || 0;
      
      // No Studio, o campo de input influencia o fluxo
      if (viewMode === 'studio') {
        this.vx += grid[gx][gy].vx * 0.08; 
        this.vy += grid[gx][gy].vy * 0.08;
      }
    }

    // Interação de Mouse
    if (isMouseDown && viewMode === 'studio') {
      const dx = this.x - mousePos.x;
      const dy = this.y - mousePos.y;
      const d = Math.sqrt(dx * dx + dy * dy);
      const influenceRadius = 250 * depthSpeed;

      if (d < influenceRadius) {
        const force = (influenceRadius - d) / influenceRadius;
        const mDX = mousePos.x - lastMousePos.x;
        const mDY = mousePos.y - lastMousePos.y;
        this.accelX += (mDX * force * 0.025); 
        this.accelY += (mDY * force * 0.025);
        if (this.z < 0.3) this.color = '#ffffff';
      }
    }

    // INTERAÇÃO COM MEMÓRIA COLETIVA (DYNAMICS)
    const m = this.memoryEnergy;
    if (m > 0.05) {
      if (m > 0.61) {
        // NÚCLEO: Consumo (reset)
        this.reset(width, height);
        return;
      } else if (m > 0.3) {
        // BORDA: Reflexão + Fluxo Tangencial
        const eR = memoryGrid[gx+1]?.[gy]?.energy || m;
        const eL = memoryGrid[gx-1]?.[gy]?.energy || m;
        const eD = memoryGrid[gx]?.[gy+1]?.energy || m;
        const eU = memoryGrid[gx]?.[gy-1]?.energy || m;
        
        const gradX = eR - eL;
        const gradY = eD - eU;
        const len = Math.hypot(gradX, gradY) || 1;
        const nx = gradX / len;
        const ny = gradY / len;
        
        // Reflexão suave
        const dot = this.vx * nx + this.vy * ny;
        this.vx -= 1.8 * dot * nx;
        this.vy -= 1.8 * dot * ny;
        
        // Fluxo tangencial
        this.vx += (-ny) * 0.25;
        this.vy += nx * 0.25;
        
        this.vx *= 0.9;
        this.vy *= 0.9;
        this.hasPath = true;
      } else {
        // EXTERIOR: Atração por gradiente
        const eR = memoryGrid[gx+1]?.[gy]?.energy || m;
        const eL = memoryGrid[gx-1]?.[gy]?.energy || m;
        const eD = memoryGrid[gx]?.[gy+1]?.energy || m;
        const eU = memoryGrid[gx]?.[gy-1]?.energy || m;
        
        this.vx += (eR - eL) * 0.15;
        this.vy += (eD - eU) * 0.15;
        this.vx *= 0.98;
        this.vy *= 0.98;
      }
    }

    // FASE FIX (Apenas no Studio, para converge ao traço local)
    if (phase === 'FIX' && viewMode === 'studio' && resampledPath && resampledPath.length > 10) {
      const fixElapsed = elapsed - DRAW_TIME;
      const fixStrength = Math.pow(Math.max(0, 1 - fixElapsed / 1000), 1.5);
      
      const { index } = distanceToPath(this.x, this.y, resampledPath);
      const target = resampledPath[index];
      const targetRadius = (target.r || 12) * 1.5;
      const dx = this.x - target.x;
      const dy = this.y - target.y;
      const currentDist = Math.hypot(dx, dy) || 1;

      if (fixStrength > 0.01) {
        let ease = 0.2 * fixStrength;
        let followX = target.x + (dx / currentDist) * targetRadius;
        let followY = target.y + (dy / currentDist) * targetRadius;

        // EXPLOSIVE FIX (Single Variation)
        if (fixElapsed < 200) {
          this.vx += (dx / currentDist) * 12;
          this.vy += (dy / currentDist) * 12;
        }

        this.vx += (followX - this.x) * ease;
        this.vy += (followY - this.y) * ease;
        this.vx *= (0.75 + (1 - fixStrength) * 0.2);
        this.vy *= (0.75 + (1 - fixStrength) * 0.2);
        this.hasPath = true;
      } else {
        this.hasPath = false;
      }
      this.color = this.baseColor;
    } else {
      if (this.color === '#ffffff' && !isMouseDown) this.color = this.baseColor;
    }

    this.accelX *= 0.85;
    this.accelY *= 0.85;
    this.vx *= this.friction;
    this.vy *= this.friction;
    
    this.x += this.vx;
    this.y += this.vy;

    // CANVAS BORDERS (No jump/Torus, for better aesthetic focus)
    if (this.x < -20 || this.x > width + 20 || this.y < -20 || this.y > height + 20) {
      this.reset(width, height);
    }
  }
}

export default function App() {
  const glCanvasRef = useRef<HTMLCanvasElement>(null);
  const bufferCanvasRef = useRef<HTMLCanvasElement>(null);
  const energyCanvasRef = useRef<HTMLCanvasElement>(null);
  const [isFixPhase, setIsFixPhase] = useState(false);
  const [viewMode, setViewMode] = useState<'studio' | 'artifact'>('studio');
  const [user, setUser] = useState<User | null>(null);
  const [activeUsers, setActiveUsers] = useState(1);
  const [showHud, setShowHud] = useState(true);
  
  const particlesRef = useRef<Particle[]>([]);
  const gridRef = useRef<any[][]>([]);
  const memoryGridRef = useRef<any[][]>([]);
  const mousePosRef = useRef({ x: 0, y: 0 });
  const lastMousePosRef = useRef({ x: 0, y: 0 });
  const isMouseDownRef = useRef(false);
  const strokePathRef = useRef<{ x: number, y: number, r: number, strokeId: number }[]>([]);
  const resampledPathRef = useRef<{ x: number, y: number, r: number, strokeId: number }[] | null>(null);
  const collectivePathRef = useRef<{ x: number, y: number, r: number, strokeId: number }[] | null>(null);
  const sharedEnergyRef = useRef<Float32Array>(new Float32Array(50 * 50));
  const targetEnergyRef = useRef<Float32Array>(new Float32Array(50 * 50));
  const wsRef = useRef<WebSocket | null>(null);
  const lastSendTimeRef = useRef(0);
  const currentStrokeIdRef = useRef(0);
  const lastPushedStrokeIdRef = useRef(-1);
  const startTimeRef = useRef(Date.now());
  const hudTimeoutRef = useRef<number | null>(null);
  
  const programRef = useRef<WebGLProgram | null>(null);
  const texturesRef = useRef<{ particle: WebGLTexture | null, energy: WebGLTexture | null }>({ particle: null, energy: null });
  const bufferRef = useRef<WebGLBuffer | null>(null);

  // WebSocket & Presence
  useEffect(() => {
    const protocol = window.location.protocol === 'https:' ? 'wss:' : 'ws:';
    const host = window.location.host;
    const ws = new WebSocket(`${protocol}//${host}`);
    ws.binaryType = "arraybuffer";
    wsRef.current = ws;

    ws.onmessage = (event) => {
      if (event.data instanceof ArrayBuffer) {
        const view = new Uint8Array(event.data);
        for (let i = 0; i < targetEnergyRef.current.length; i++) {
          // Normalização e ganho extra para visibilidade
          targetEnergyRef.current[i] = Math.min(1.0, (view[i] / 255) * 1.2);
        }
      }
    };

    ws.onclose = () => {
      console.log("WebSocket closed. Attempting reconnect...");
    };

    signInAnonymously(auth).catch(err => {
      if (err.code === 'auth/admin-restricted-operation') {
        console.warn("Anonymous Auth disabled in Firebase Console. Collective presence features (active user count) might not work, but WebSocket energy remains functional.");
      } else {
        console.error("Auth error:", err);
      }
    });
    onAuthStateChanged(auth, (u) => {
      setUser(u);
      if (u) {
        const updatePresence = () => {
          setDoc(doc(db, 'presence', u.uid), { lastActive: serverTimestamp() });
        };
        updatePresence();
        const interval = setInterval(updatePresence, 5000);
        return () => clearInterval(interval);
      }
    });

    const q = query(collection(db, 'presence'));
    const unsubscribe = onSnapshot(q, (snapshot) => {
      const now = Date.now();
      const count = snapshot.docs.filter(d => {
        const data = d.data();
        if (!data.lastActive) return false;
        return (now - data.lastActive.toMillis()) < 20000;
      }).length;
      setActiveUsers(Math.max(1, count));
    });
    return () => {
      unsubscribe();
      ws.close();
    };
  }, []);

  // HUD Visibility
  useEffect(() => {
    if (viewMode === 'artifact') {
      const timer = setTimeout(() => setShowHud(false), 2000);
      hudTimeoutRef.current = timer as unknown as number;
      return () => clearTimeout(timer);
    } else {
      setShowHud(true);
    }
  }, [viewMode]);

  const toggleMode = () => {
    setViewMode(prev => prev === 'studio' ? 'artifact' : 'studio');
    setShowHud(true);
  };

  const handleInteraction = useCallback(() => {
    if (viewMode === 'artifact') {
      setShowHud(true);
      if (hudTimeoutRef.current) clearTimeout(hudTimeoutRef.current);
      hudTimeoutRef.current = setTimeout(() => setShowHud(false), 2000) as unknown as number;
    }
  }, [viewMode]);

  useEffect(() => {
    const glCanvas = glCanvasRef.current;
    const bufferCanvas = bufferCanvasRef.current;
    const energyCanvas = energyCanvasRef.current;
    if (!glCanvas || !bufferCanvas || !energyCanvas) return;

    const bctx = bufferCanvas.getContext('2d', { alpha: false });
    const gl = glCanvas.getContext('webgl');
    if (!bctx || !gl) return;

    const init = () => {
      const width = VIRTUAL_WIDTH;
      const height = VIRTUAL_HEIGHT;
      
      // Resolução interna fixa para consistência
      glCanvas.width = bufferCanvas.width = width;
      glCanvas.height = bufferCanvas.height = height;

      gl.viewport(0, 0, width, height);

      const cols = Math.ceil(width / GRID_RES) + 1;
      const rows = Math.ceil(height / GRID_RES) + 1;
      energyCanvas.width = cols;
      energyCanvas.height = rows;
      
      gridRef.current = Array.from({ length: cols }, () => 
        Array.from({ length: rows }, () => ({ vx: 0, vy: 0, energy: 0 }))
      );
      memoryGridRef.current = Array.from({ length: cols }, () => 
        Array.from({ length: rows }, () => ({ vx: 0, vy: 0, energy: 0 }))
      );

      particlesRef.current = Array.from({ length: PARTICLE_COUNT }, () => new Particle(width, height));
      particlesRef.current.sort((a, b) => b.z - a.z);
    };

    const initGL = () => {
      const createShader = (type: number, source: string) => {
        const s = gl.createShader(type)!;
        gl.shaderSource(s, source);
        gl.compileShader(s);
        return s;
      };

      const vs = createShader(gl.VERTEX_SHADER, V_SHADER_SOURCE);
      const fs = createShader(gl.FRAGMENT_SHADER, F_SHADER_SOURCE);
      const program = gl.createProgram()!;
      gl.attachShader(program, vs);
      gl.attachShader(program, fs);
      gl.linkProgram(program);
      gl.useProgram(program);
      programRef.current = program;

      const buffer = gl.createBuffer();
      gl.bindBuffer(gl.ARRAY_BUFFER, buffer);
      // Quad padrão (2 triângulos) cobrindo -1 a 1
      gl.bufferData(gl.ARRAY_BUFFER, new Float32Array([-1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, 1]), gl.STATIC_DRAW);
      bufferRef.current = buffer;

      const pos = gl.getAttribLocation(program, "a_position");
      gl.enableVertexAttribArray(pos);
      gl.vertexAttribPointer(pos, 2, gl.FLOAT, false, 0, 0);

      texturesRef.current.particle = gl.createTexture();
      texturesRef.current.energy = gl.createTexture();
    };

    const updateTexture = (tex: WebGLTexture | null, source: HTMLCanvasElement, unit: number) => {
      if (!tex) return;
      gl.activeTexture(gl.TEXTURE0 + unit);
      gl.bindTexture(gl.TEXTURE_2D, tex);
      gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, gl.RGBA, gl.UNSIGNED_BYTE, source);
      gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
      gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
      gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
      gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
    };

    const applyForce = (x: number, y: number, vx: number, vy: number, energyScale: number = 1.0) => {
      if (!gridRef.current.length) return;
      const gx = Math.floor(x / GRID_RES);
      const gy = Math.floor(y / GRID_RES);
      const cols = gridRef.current.length;
      const rows = gridRef.current[0].length;
      const radius = 6; 
      const maxForce = 45;
      const limitedVX = Math.max(-maxForce, Math.min(maxForce, vx));
      const limitedVY = Math.max(-maxForce, Math.min(maxForce, vy));

      for (let i = -radius; i <= radius; i++) {
        for (let j = -radius; j <= radius; j++) {
          const nx = gx + i, ny = gy + j;
          if (nx >= 0 && nx < cols && ny >= 0 && ny < rows) {
            const dSq = i * i + j * j;
            if (dSq > radius * radius) continue;

            const f = Math.exp(-dSq / 12.0); 
            gridRef.current[nx][ny].vx += limitedVX * f * 0.5;
            gridRef.current[nx][ny].vy += limitedVY * f * 0.5;
            
            const energyAdd = f * 0.6 * energyScale;
            const newEnergy = gridRef.current[nx][ny].energy + energyAdd;
            gridRef.current[nx][ny].energy = Math.min(1.0, newEnergy);
            
            // Send to collective mind server with Throttling
            const now = Date.now();
            if (i === 0 && j === 0 && wsRef.current?.readyState === WebSocket.OPEN && now - lastSendTimeRef.current > 40) {
              const normX = x / VIRTUAL_WIDTH;
              const normY = y / VIRTUAL_HEIGHT;
              wsRef.current.send(JSON.stringify({
                type: 'impulse',
                x: normX,
                y: normY,
                intensity: 0.35,
                vx: limitedVX * 0.1,
                vy: limitedVY * 0.1
              }));
              lastSendTimeRef.current = now;
            }
          }
        }
      }
    };

    const animate = () => {
      const glCanvas = glCanvasRef.current;
      const energyCanvas = energyCanvasRef.current;
      const bufferCanvas = bufferCanvasRef.current;
      if (!glCanvas || !energyCanvas || !bufferCanvas || !programRef.current) {
        requestAnimationFrame(animate);
        return;
      }

      const gl = glCanvas.getContext('webgl')!;
      const bctx = bufferCanvas.getContext('2d')!;

      const currentWidth = glCanvas.width;
      const currentHeight = glCanvas.height;
      if (currentWidth <= 0 || currentHeight <= 0) {
        requestAnimationFrame(animate);
        return;
      }

      const cols = energyCanvas.width;
      const rows = energyCanvas.height;

      const now = Date.now();
      const elapsed = now % CYCLE_TIME;
      const isFix = elapsed >= DRAW_TIME;
      const phase = isFix ? 'FIX' : 'DRAW';
      setIsFixPhase(isFix);

      document.documentElement.style.setProperty('--progress', `${(elapsed / DRAW_TIME) * 100}%`);

      if (phase === 'FIX' && !resampledPathRef.current && (viewMode === 'studio' ? strokePathRef.current.length > 5 : collectivePathRef.current)) {
        if (viewMode === 'studio') {
          resampledPathRef.current = resamplePath(strokePathRef.current, 3);
        } else {
          resampledPathRef.current = collectivePathRef.current;
        }
      }

      if (phase === 'DRAW') {
        resampledPathRef.current = null;
      }

      gl.viewport(0, 0, currentWidth, currentHeight);
      gl.clearColor(0, 0, 0, 1);
      gl.clear(gl.COLOR_BUFFER_BIT);

      bctx.fillStyle = '#010101';
      bctx.fillRect(0, 0, currentWidth, currentHeight);

      // --- MODO APRESENTAÇÃO: AURA COLETIVA ---
      // Desenha a "névoa" da memória antes das partículas
      if (viewMode === 'artifact') {
        const cw = currentWidth / cols;
        const ch = currentHeight / rows;
        for (let x = 0; x < cols; x += 2) { // Step 2 para performance
          for (let y = 0; y < rows; y += 2) {
            const m = memoryGridRef.current[x][y].energy;
            if (m > 0.1) {
              const alpha = Math.pow(m, 2) * 0.15;
              bctx.fillStyle = `rgba(100, 200, 255, ${alpha})`; // Aura levemente azulada
              bctx.beginPath();
              bctx.arc(x * cw, y * ch, cw * 3 * m, 0, Math.PI * 2);
              bctx.fill();
            }
          }
        }
      }

      // Process signals
      if (!isFix && strokePathRef.current.length > 0 && elapsed < 100) strokePathRef.current = [];

      // Group particles by color and quantized Z for batching (depth aesthetics)
      const groups: Record<string, Particle[]> = {};
      
      for (let i = 0; i < particlesRef.current.length; i++) {
        const p = particlesRef.current[i];
        p.update(
          currentWidth, currentHeight, phase, gridRef.current, memoryGridRef.current,
          mousePosRef.current, lastMousePosRef.current, 
          isMouseDownRef.current, resampledPathRef.current,
          elapsed, viewMode
        );
        
        // Quantize Z and Alpha to keep depth/style aesthetics while batching
        const zKey = Math.floor(p.z * 5);
        const speed = Math.hypot(p.vx, p.vy);
        const memVisual = Math.pow(p.memoryEnergy, 1.6);
        let alpha = (0.2 + speed * 1.5 + p.energy * 0.5 + memVisual * 1.5) * (1 - (p.z * 0.6));
        const aKey = Math.floor(Math.min(0.9, alpha) * 10);
        
        const key = `${p.color}_${zKey}_${aKey}_${p.hasPath}`;
        if (!groups[key]) groups[key] = [];
        groups[key].push(p);
      }

      // Batched Drawing per Group
      bctx.lineCap = 'round';
      for (const key in groups) {
        const p0 = groups[key][0];
        const s = 1 - (p0.z * 0.6);
        
        // Re-calculate alpha for the group (using p0 as representative)
        const speed0 = Math.hypot(p0.vx, p0.vy);
        const memVisual0 = Math.pow(p0.memoryEnergy, 1.6);
        let alpha0 = (0.18 + speed0 * 1.2 + (viewMode === 'artifact' ? memVisual0 * 1.8 : p0.energy * 0.5)) * s;
        if (viewMode === 'artifact') alpha0 = Math.min(0.95, alpha0 * (0.4 + memVisual0 * 2.5));

        bctx.strokeStyle = p0.color;
        bctx.lineWidth = (p0.hasPath ? 3.5 : 1.4 + (1 - p0.z) * 1.8) * s;
        bctx.globalAlpha = Math.min(0.8, alpha0);
        
        bctx.beginPath();
        groups[key].forEach(p => {
          bctx.moveTo(p.px, p.py);
          bctx.lineTo(p.x, p.y);
        });
        bctx.stroke();
      }

      const ectx = energyCanvas.getContext('2d')!;
      const id = ectx.createImageData(cols, rows);

      for (let x = 0; x < cols; x++) {
        const col = gridRef.current[x];
        const mCol = memoryGridRef.current[x];
        const colR = gridRef.current[x + 1];
        const colL = gridRef.current[x - 1];
        const mColR = memoryGridRef.current[x + 1];
        const mColL = memoryGridRef.current[x - 1];

        // Shared energy mapping
        const nx = Math.min(49, Math.floor((x / cols) * 50));

        for (let y = 0; y < rows; y++) {
          const cell = col[y];
          const mem = mCol[y];
          
          const ny = Math.min(49, Math.floor((y / rows) * 50));
          const netIdx = ny * 50 + nx;
          
          // Smoothen network data (Lerp)
          sharedEnergyRef.current[netIdx] += (targetEnergyRef.current[netIdx] - sharedEnergyRef.current[netIdx]) * 0.1;
          const remoteEnergy = sharedEnergyRef.current[netIdx];

          cell.vx *= 0.94;
          cell.vy *= 0.94;
          
          const e = cell.energy;
          const m = mem.energy;

          // 1. inputField decay e difusão
          const cR = colR ? colR[y].energy : e;
          const cL = colL ? colL[y].energy : e;
          const cD = col[y + 1] ? col[y + 1].energy : e;
          const cU = col[y - 1] ? col[y - 1].energy : e;
          const avgCell = (e + cR + cL + cD + cU) * 0.2;
          cell.energy = (e + (avgCell - e) * 0.2) * 0.88;

          // 2. Integração contínua com inércia (f1 & f5)
          // Combina input local com energia remota (mais sensível à rede)
          const combinedInput = Math.max(e, remoteEnergy * 0.9);
          mem.energy += (combinedInput - m) * (0.07 + combinedInput * 0.15);

          // 3. Decay suave (f2)
          mem.energy *= 0.998; // Mantém a memória por mais tempo

          // 4. Suavização espacial (Evitando alocações de array) (f3)
          const mR = mColR ? mColR[y].energy : m;
          const mL = mColL ? mColL[y].energy : m;
          const mD = mCol[y + 1] ? mCol[y + 1].energy : m;
          const mU = mCol[y - 1] ? mCol[y - 1].energy : m;
          
          const avgMem = (m + mR + mL + mD + mU) * 0.2;
          mem.energy += (avgMem - mem.energy) * 0.2;
          
          mem.energy = Math.min(1.0, Math.max(0, mem.energy));

          // 5. Curva visual (Combinação de input local e memória coletiva)
          const displayVal = Math.max(cell.energy, Math.pow(mem.energy, 1.6));

          const idx = (y * cols + x) * 4;
          const val = displayVal * 255;
          id.data[idx] = val;
          id.data[idx + 1] = val;
          id.data[idx + 2] = val;
          id.data[idx + 3] = 255;
        }
      }
      ectx.putImageData(id, 0, 0);

      gl.useProgram(programRef.current);
      
      updateTexture(texturesRef.current.particle, bufferCanvas, 0);
      updateTexture(texturesRef.current.energy, energyCanvas, 1);
      
      const fixFactor = viewMode === 'artifact' ? 0.8 : (phase === 'FIX' ? Math.pow(Math.max(0, 1 - (elapsed - DRAW_TIME) / 1000), 2) : 0);
      
      gl.uniform1i(gl.getUniformLocation(programRef.current, "u_tex"), 0);
      gl.uniform1i(gl.getUniformLocation(programRef.current, "u_energy"), 1);
      gl.uniform1f(gl.getUniformLocation(programRef.current, "u_time"), now * 0.001);
      gl.uniform1f(gl.getUniformLocation(programRef.current, "u_fixFactor"), fixFactor);

      if (bufferRef.current) {
        gl.bindBuffer(gl.ARRAY_BUFFER, bufferRef.current);
        const posAttr = gl.getAttribLocation(programRef.current, "a_position");
        gl.enableVertexAttribArray(posAttr);
        gl.vertexAttribPointer(posAttr, 2, gl.FLOAT, false, 0, 0);
      }
      
      gl.drawArrays(gl.TRIANGLES, 0, 6);

      requestAnimationFrame(animate);
    };

    const handleInput = (clientX: number, clientY: number, active: boolean) => {
      const glCanvas = glCanvasRef.current;
      if (!glCanvas) return;

      const rect = glCanvas.getBoundingClientRect();
      // Mapeia coordenadas da tela para o espaço interno 1080x1920
      const scaleX = VIRTUAL_WIDTH / rect.width;
      const scaleY = VIRTUAL_HEIGHT / rect.height;
      const x = (clientX - rect.left) * scaleX;
      const y = (clientY - rect.top) * scaleY;

      const lx = mousePosRef.current.x;
      const ly = mousePosRef.current.y;
      lastMousePosRef.current = { x: lx, y: ly };
      mousePosRef.current = { x, y };
      
      const wasMouseDown = isMouseDownRef.current;
      isMouseDownRef.current = active;

      if (isMouseDownRef.current) {
        const dx = x - lx;
        const dy = y - ly;
        const dist = Math.hypot(dx, dy);
        
        // Interpolação robusta: garante que o rastro seja contínuo independente da velocidade
        if (wasMouseDown && dist > 1.0) {
          const steps = Math.max(1, Math.min(25, Math.ceil(dist / 2)));
          for (let i = 1; i <= steps; i++) {
            const lerpX = lx + (dx * (i / steps));
            const lerpY = ly + (dy * (i / steps));
            // Injeta a força na direção do movimento (dx, dy)
            applyForce(lerpX, lerpY, dx, dy, 1.0 / steps);
          }
        } else {
          applyForce(x, y, dx, dy, 1.0);
        }

        const elapsed = Date.now() % CYCLE_TIME;
        if (elapsed < DRAW_TIME) {
          const lastPoint = strokePathRef.current[strokePathRef.current.length - 1];
          if (!lastPoint || Math.hypot(x - lastPoint.x, y - lastPoint.y) > 8) {
            const dx = x - lx;
            const dy = y - ly;
            const speed = Math.hypot(dx, dy);
            const radius = Math.max(14, Math.min(48, 16 + speed * 2.5));
            strokePathRef.current.push({ x, y, r: radius, strokeId: currentStrokeIdRef.current });
          }
        }
      }
    };

    const handleMouseMove = (e: MouseEvent) => handleInput(e.clientX, e.clientY, isMouseDownRef.current);
    const handleMouseDown = (e: MouseEvent) => {
      currentStrokeIdRef.current++;
      handleInput(e.clientX, e.clientY, true);
    };
    const handleMouseUp = () => isMouseDownRef.current = false;

    const handleTouchMove = (e: TouchEvent) => {
      e.preventDefault();
      handleInput(e.touches[0].clientX, e.touches[0].clientY, true);
    };
    const handleTouchStart = (e: TouchEvent) => {
      currentStrokeIdRef.current++;
      handleInput(e.touches[0].clientX, e.touches[0].clientY, true);
    };
    const handleTouchEnd = () => isMouseDownRef.current = false;

    window.addEventListener('mousedown', handleMouseDown);
    window.addEventListener('mouseup', handleMouseUp);
    window.addEventListener('mousemove', handleMouseMove);
    window.addEventListener('touchstart', handleTouchStart, { passive: false });
    window.addEventListener('touchend', handleTouchEnd);
    window.addEventListener('touchmove', handleTouchMove, { passive: false });
    window.addEventListener('click', handleInteraction);
    window.addEventListener('touchstart', handleInteraction);

    init();
    initGL();
    animate();

    return () => {
      window.removeEventListener('mousedown', handleMouseDown);
      window.removeEventListener('mouseup', handleMouseUp);
      window.removeEventListener('mousemove', handleMouseMove);
      window.removeEventListener('touchstart', handleTouchStart);
      window.removeEventListener('touchend', handleTouchEnd);
      window.removeEventListener('touchmove', handleTouchMove);
      window.removeEventListener('click', handleInteraction);
      window.removeEventListener('touchstart', handleInteraction);
    };
  }, [viewMode, handleInteraction]);

  return (
    <div className="fixed inset-0 overflow-hidden bg-zinc-950 flex items-center justify-center select-none outline-none">
      <div className="relative aspect-[9/16] h-full max-h-screen max-w-full shadow-2xl">
        <canvas 
          ref={glCanvasRef} 
          className="w-full h-full block bg-black" 
          style={{ objectFit: 'contain' }}
        />
        <canvas ref={bufferCanvasRef} style={{ display: 'none' }} />
        <canvas ref={energyCanvasRef} style={{ display: 'none' }} />

        {/* HUD UI */}
        <div className={`absolute inset-0 z-20 pointer-events-none transition-opacity duration-1000 ${showHud ? 'opacity-100' : 'opacity-0'}`}>
          <div className={`absolute top-12 left-1/2 -translate-x-1/2 pointer-events-none text-center ${isFixPhase ? 'is-fixing' : ''}`}>
            <div className="draw-container font-sans">
              {isFixPhase ? 'FIX' : 'DRAW'}
              <div className="draw-fill">{isFixPhase ? 'FIX' : 'DRAW'}</div>
            </div>
          </div>

          <div className="absolute bottom-12 left-0 right-0 px-8 flex justify-between items-end pointer-events-auto">
            <div className="flex flex-col gap-4">
              <div className="flex items-center gap-3 text-zinc-400 font-mono text-[10px] tracking-wider uppercase">
                <div className="w-1.5 h-1.5 bg-[#34a853] rounded-full animate-pulse shadow-[0_0_8px_#34a853]" />
                {activeUsers} Online
              </div>
            </div>
          </div>
        </div>
      </div>
    </div>
  );
}
