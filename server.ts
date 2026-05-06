import express from "express";
import { WebSocketServer, WebSocket } from "ws";
import { createServer as createViteServer } from "vite";
import path from "path";

async function startServer() {
  const app = express();
  const PORT = 3000;

  // Collective Grid State
  const GRID_SIZE = 50;
  const globalEnergy = new Float32Array(GRID_SIZE * GRID_SIZE);

  // WebSocket Server
  const wss = new WebSocketServer({ noServer: true });

  // 15Hz Broadcast of the Collective Force Field
  setInterval(() => {
    let hasActivity = false;
    // Layout: [Energy (Uint8), VX (Int8), VY (Int8)]
    const size = GRID_SIZE * GRID_SIZE;
    const buffer = new ArrayBuffer(size * 3);
    const energyView = new Uint8Array(buffer, 0, size);
    const vxView = new Int8Array(buffer, size, size);
    const vyView = new Int8Array(buffer, size * 2, size);

    for (let i = 0; i < size; i++) {
      if (globalEnergy[i] > 0.005) {
        globalEnergy[i] *= 0.991; 
        hasActivity = true;
      } else {
        globalEnergy[i] = 0;
      }
      
      energyView[i] = Math.min(255, globalEnergy[i] * 255);
      // For now, we simulate shared force dynamics by local derived velocity, 
      // but we can pass vx/vy if we expand the server grid state.
      // To keep it light, we'll focus on energy sync for now which influences flow.
    }

    if (hasActivity) {
      const payload = Buffer.from(buffer);
      wss.clients.forEach((client) => {
        if (client.readyState === WebSocket.OPEN) {
          client.send(payload);
        }
      });
    }
  }, 1000 / 15);

  wss.on("connection", (ws) => {
    ws.on("message", (message) => {
      try {
        const data = JSON.parse(message.toString());
        if (data.type === 'impulse') {
          const gx = Math.floor(data.x * GRID_SIZE);
          const gy = Math.floor(data.y * GRID_SIZE);

          if (gx >= 0 && gx < GRID_SIZE && gy >= 0 && gy < GRID_SIZE) {
            const idx = gy * GRID_SIZE + gx;
            globalEnergy[idx] = Math.min(1.0, globalEnergy[idx] + data.intensity);
          }
        }
      } catch (e) {}
    });
  });

  // Vite integration
  if (process.env.NODE_ENV !== "production") {
    const vite = await createViteServer({
      server: { middlewareMode: true },
      appType: "spa",
    });
    app.use(vite.middlewares);
  } else {
    const distPath = path.join(process.cwd(), "dist");
    app.use(express.static(distPath));
    app.get("*", (req, res) => {
      res.sendFile(path.join(distPath, "index.html"));
    });
  }

  // Handle WebSocket upgrades
  const httpServer = app.listen(PORT, "0.0.0.0", () => {
    console.log(`Collective engine running on http://localhost:${PORT}`);
  });

  httpServer.on("upgrade", (request, socket, head) => {
    wss.handleUpgrade(request, socket, head, (ws) => {
      wss.emit("connection", ws, request);
    });
  });
}

startServer();
