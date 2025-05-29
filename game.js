const canvas = document.getElementById('gameCanvas');
const ctx = canvas.getContext('2d');
const CELL_SIZE = 20;
const GRID_WIDTH = 30;
const GRID_HEIGHT = 20;

canvas.width = GRID_WIDTH * CELL_SIZE;
canvas.height = GRID_HEIGHT * CELL_SIZE;

// Game state with better balanced speeds
let game = {
    score: 0,
    level: 1,
    lives: 3,
    multiplier: 1,
    isPlaying: true,
    isPaused: false,
    playerSpeed: 12,  // Slower for better balance
    enemySpeed: 16,   // Slower enemy speed for more strategic gameplay
    dotsCollected: 0,
    totalDots: 0,
    powerPelletActive: false,
    powerPelletTimer: 0,
    difficulty: 1.0,
    comboCounter: 0,
    lastDotTime: 0,
    basePlayerSpeed: 12,
    baseEnemySpeed: 16,
    maxSpeedIncrease: 8  // Limit speed increases for balance
};

// Player
let player = {
    x: 1,
    y: 1,
    moveTimer: 0,
    direction: { x: 0, y: 0 }
};

// Enemies
let enemies = [];

// Grid
let grid = [];

// Enhanced pathfinding cache with TTL and size limits
let pathfindingCache = new Map();
let cacheStats = { hits: 0, misses: 0, size: 0 };
const MAX_CACHE_SIZE = 500;
const CACHE_TTL = 5000; // 5 seconds

// Performance monitoring and theme tracking
let performanceStats = {
    lastFrameTime: Date.now(),
    frameCount: 0,
    fps: 60
};

let currentTheme = 'classic';

// Enhanced A* pathfinding with improved heuristics and cache management
function findPath(startX, startY, endX, endY) {
    const key = `${startX},${startY}-${endX},${endY}`;
    const cached = pathfindingCache.get(key);
    
    // Check cache with TTL
    if (cached && Date.now() - cached.timestamp < CACHE_TTL) {
        cacheStats.hits++;
        return cached.path;
    }
    
    cacheStats.misses++;
    
    // Manage cache size
    if (pathfindingCache.size >= MAX_CACHE_SIZE) {
        const oldestKey = pathfindingCache.keys().next().value;
        pathfindingCache.delete(oldestKey);
    }

    // Early exit for same position
    if (startX === endX && startY === endY) {
        return [];
    }

    // Early exit if target is unreachable (wall)
    if (grid[endY] && grid[endY][endX] === 1) {
        pathfindingCache.set(key, { path: null, timestamp: Date.now() });
        return null;
    }

    const openSet = [{x: startX, y: startY, g: 0, h: 0, f: 0, parent: null}];
    const closedSet = new Set();
    const openSetMap = new Map();
    openSetMap.set(`${startX},${startY}`, openSet[0]);
    
    // Improved heuristic - consider both Manhattan and diagonal distance
    function heuristic(x1, y1, x2, y2) {
        const dx = Math.abs(x1 - x2);
        const dy = Math.abs(y1 - y2);
        return dx + dy + Math.min(dx, dy) * 0.1; // Slight preference for diagonal paths
    }
    
    while (openSet.length > 0) {
        // More efficient way to find minimum f-score
        let currentIndex = 0;
        for (let i = 1; i < openSet.length; i++) {
            if (openSet[i].f < openSet[currentIndex].f) {
                currentIndex = i;
            }
        }
        
        let current = openSet[currentIndex];
        
        // Remove current from open set
        openSet.splice(currentIndex, 1);
        openSetMap.delete(`${current.x},${current.y}`);
        closedSet.add(`${current.x},${current.y}`);
        
        // Check if we reached the goal
        if (current.x === endX && current.y === endY) {
            let path = [];
            while (current.parent) {
                path.unshift({x: current.x, y: current.y});
                current = current.parent;
            }
            pathfindingCache.set(key, { path: path, timestamp: Date.now() });
            return path;
        }
        
        // Check neighbors with improved movement costs
        const neighbors = [
            {x: current.x + 1, y: current.y, cost: 1},
            {x: current.x - 1, y: current.y, cost: 1},
            {x: current.x, y: current.y + 1, cost: 1},
            {x: current.x, y: current.y - 1, cost: 1}
        ];
        
        for (let neighbor of neighbors) {
            const neighborKey = `${neighbor.x},${neighbor.y}`;
            
            if (neighbor.x < 0 || neighbor.x >= GRID_WIDTH || 
                neighbor.y < 0 || neighbor.y >= GRID_HEIGHT ||
                grid[neighbor.y][neighbor.x] === 1 ||
                closedSet.has(neighborKey)) {
                continue;
            }
            
            let g = current.g + neighbor.cost;
            let h = heuristic(neighbor.x, neighbor.y, endX, endY);
            let f = g + h;
            
            let existing = openSetMap.get(neighborKey);
            if (!existing) {
                const newNode = {
                    x: neighbor.x, 
                    y: neighbor.y, 
                    g: g, 
                    h: h, 
                    f: f, 
                    parent: current
                };
                openSet.push(newNode);
                openSetMap.set(neighborKey, newNode);
            } else if (g < existing.g) {
                existing.g = g;
                existing.f = g + existing.h;
                existing.parent = current;
            }
        }
    }
    
    pathfindingCache.set(key, { path: null, timestamp: Date.now() });
    return null; // No path found
}

// Enhanced procedural level generation with biomes and special features
function generateLevel(level) {
    grid = Array(GRID_HEIGHT).fill().map(() => Array(GRID_WIDTH).fill(0));
    pathfindingCache.clear(); // Clear cache for new level
    
    // Determine level theme/biome
    const themes = ['classic', 'fortress', 'labyrinth', 'chambers', 'spiral'];
    const theme = themes[Math.min(themes.length - 1, Math.floor((level - 1) / 3))];
    
    // Create border walls
    for (let y = 0; y < GRID_HEIGHT; y++) {
        for (let x = 0; x < GRID_WIDTH; x++) {
            if (x === 0 || x === GRID_WIDTH - 1 || y === 0 || y === GRID_HEIGHT - 1) {
                grid[y][x] = 1;
            }
        }
    }
    
    // Generate themed maze
    generateThemedMaze(level, theme);
    
    // Add special features based on level
    addSpecialFeatures(level);
    
    // Ensure connectivity with improved algorithm
    ensureConnectivity();
    
    // Place strategic power pellets
    placePowerPellets(level);
    
    // Place dots and count them
    placeDots();
    
    // Clear starting areas
    clearStartingAreas();
    
    // Generate enemies with advanced behaviors
    generateAdvancedEnemies(level);
    
    // Update difficulty scaling with better balance
    updateBalancedDifficulty(level);
}

function generateMaze(level) {
    // Create a more interesting maze with varying complexity based on level
    const complexity = Math.min(0.8, 0.3 + level * 0.05);
    divideChamber(1, 1, GRID_WIDTH - 2, GRID_HEIGHT - 2, complexity);
    
    // Add some random walls for variety
    const extraWalls = Math.floor(level / 3);
    for (let i = 0; i < extraWalls; i++) {
        let x = Math.floor(Math.random() * (GRID_WIDTH - 4)) + 2;
        let y = Math.floor(Math.random() * (GRID_HEIGHT - 4)) + 2;
        if (grid[y][x] === 0) {
            grid[y][x] = 1;
        }
    }
}

function ensureConnectivity() {
    // Simple flood fill to ensure all areas are reachable
    let visited = Array(GRID_HEIGHT).fill().map(() => Array(GRID_WIDTH).fill(false));
    let queue = [{x: 1, y: 1}];
    visited[1][1] = true;
    
    while (queue.length > 0) {
        let {x, y} = queue.shift();
        const neighbors = [
            {x: x+1, y: y}, {x: x-1, y: y}, 
            {x: x, y: y+1}, {x: x, y: y-1}
        ];
        
        for (let neighbor of neighbors) {
            if (neighbor.x > 0 && neighbor.x < GRID_WIDTH-1 &&
                neighbor.y > 0 && neighbor.y < GRID_HEIGHT-1 &&
                !visited[neighbor.y][neighbor.x] && 
                grid[neighbor.y][neighbor.x] !== 1) {
                visited[neighbor.y][neighbor.x] = true;
                queue.push(neighbor);
            }
        }
    }
    
    // Connect unreachable areas
    for (let y = 1; y < GRID_HEIGHT-1; y++) {
        for (let x = 1; x < GRID_WIDTH-1; x++) {
            if (!visited[y][x] && grid[y][x] !== 1) {
                // Find nearest reachable cell and create a path
                if (x > 1 && visited[y][x-1]) grid[y][x] = 0;
                else if (y > 1 && visited[y-1][x]) grid[y][x] = 0;
            }
        }
    }
}

function placePowerPellets(level) {
    const powerPellets = Math.min(6, Math.floor(level / 2) + 2);
    const corners = [
        {x: 2, y: 2}, {x: GRID_WIDTH-3, y: 2},
        {x: 2, y: GRID_HEIGHT-3}, {x: GRID_WIDTH-3, y: GRID_HEIGHT-3}
    ];
    
    // Place some in corners for strategic gameplay
    for (let i = 0; i < Math.min(powerPellets, 4); i++) {
        if (grid[corners[i].y][corners[i].x] === 0) {
            grid[corners[i].y][corners[i].x] = 3;
        }
    }
    
    // Place remaining randomly but strategically
    let remaining = powerPellets - 4;
    while (remaining > 0) {
        let x = Math.floor(Math.random() * (GRID_WIDTH - 4)) + 2;
        let y = Math.floor(Math.random() * (GRID_HEIGHT - 4)) + 2;
        if (grid[y][x] === 0) {
            grid[y][x] = 3;
            remaining--;
        }
    }
}

function placeDots() {
    game.totalDots = 0;
    for (let y = 1; y < GRID_HEIGHT - 1; y++) {
        for (let x = 1; x < GRID_WIDTH - 1; x++) {
            if (grid[y][x] === 0) {
                grid[y][x] = 2; // dot
                game.totalDots++;
            }
        }
    }
}

function clearStartingAreas() {
    // Clear player starting area
    grid[1][1] = 0;
    grid[1][2] = 0;
    grid[2][1] = 0;
    
    // Clear enemy starting area
    grid[GRID_HEIGHT-2][GRID_WIDTH-2] = 0;
    grid[GRID_HEIGHT-2][GRID_WIDTH-3] = 0;
    grid[GRID_HEIGHT-3][GRID_WIDTH-2] = 0;
    
    player.x = 1;
    player.y = 1;
}

function generateAdvancedEnemies(level) {
    enemies = [];
    let enemyCount = Math.min(8, Math.floor(level / 2) + 2); // Cap enemy count
    
    const behaviors = ['aggressive', 'patrol', 'ambush', 'random', 'coordinator', 'trapper'];
    const colors = ['#ff4444', '#44ff44', '#4444ff', '#ffff44', '#ff44ff', '#44ffff', '#ff8844', '#8844ff'];
    
    for (let i = 0; i < enemyCount; i++) {
        enemies.push({
            x: GRID_WIDTH - 2,
            y: GRID_HEIGHT - 2,
            moveTimer: 0,
            color: colors[i % colors.length],
            scared: false,
            scaredTimer: 0,
            behavior: behaviors[i % behaviors.length],
            patrolTarget: null,
            lastDirection: {x: 0, y: 0},
            personalityTimer: Math.random() * 60,
            smartMode: false,
            cooperationLevel: Math.min(1.0, level * 0.1), // Enemies cooperate more at higher levels
            lastPlayerPosition: {x: player.x, y: player.y},
            predictionAccuracy: Math.min(0.8, level * 0.05), // Better prediction at higher levels
            id: i
        });
    }
}

function updateBalancedDifficulty(level) {
    // More gradual and balanced difficulty scaling
    game.difficulty = 1.0 + (level - 1) * 0.05; // Slower difficulty increase
    
    // Cap the speed increases to maintain playability
    const speedReduction = Math.min(game.maxSpeedIncrease, Math.floor(level / 2));
    game.enemySpeed = Math.max(8, game.baseEnemySpeed - speedReduction);
    game.playerSpeed = Math.max(6, game.basePlayerSpeed - Math.floor(speedReduction * 0.6)); // Player speed reduces slower
    
    // Add strategic elements instead of just speed
    if (level > 5) {
        // Increase enemy coordination and smarter behaviors at higher levels
        enemies.forEach(enemy => {
            if (Math.random() < 0.1 * (level - 5)) {
                enemy.smartMode = true; // Enhanced AI mode
            }
        });
    }
}

// Improved maze generation using recursive division
function divideChamber(x, y, width, height, complexity) {
    if (width < 4 || height < 4) return;
    
    let horizontal = Math.random() < 0.5;
    
    if (horizontal) {
        let wallY = y + 2 + Math.floor(Math.random() * (height - 3));
        for (let wx = x; wx < x + width; wx++) {
            grid[wallY][wx] = 1;
        }
        
        // Create multiple holes for more interesting layouts
        let holes = Math.random() < complexity ? 2 : 1;
        for (let h = 0; h < holes; h++) {
            let holeX = x + Math.floor(Math.random() * width);
            grid[wallY][holeX] = 0;
        }
        
        if (Math.random() < complexity) {
            divideChamber(x, y, width, wallY - y, complexity);
            divideChamber(x, wallY + 1, width, height - (wallY - y) - 1, complexity);
        }
    } else {
        let wallX = x + 2 + Math.floor(Math.random() * (width - 3));
        for (let wy = y; wy < y + height; wy++) {
            grid[wy][wallX] = 1;
        }
        
        // Create multiple holes for more interesting layouts
        let holes = Math.random() < complexity ? 2 : 1;
        for (let h = 0; h < holes; h++) {
            let holeY = y + Math.floor(Math.random() * height);
            grid[holeY][wallX] = 0;
        }
        
        if (Math.random() < complexity) {
            divideChamber(x, y, wallX - x, height, complexity);
            divideChamber(wallX + 1, y, width - (wallX - x) - 1, height, complexity);
        }
    }
}

function generateThemedMaze(level, theme) {
    const complexity = Math.min(0.8, 0.3 + level * 0.03); // Slower complexity increase
    
    switch (theme) {
        case 'classic':
            divideChamber(1, 1, GRID_WIDTH - 2, GRID_HEIGHT - 2, complexity);
            break;
        case 'fortress':
            generateFortressLayout(complexity);
            break;
        case 'labyrinth':
            generateLabyrinthLayout(complexity);
            break;
        case 'chambers':
            generateChamberLayout(complexity);
            break;
        case 'spiral':
            generateSpiralLayout(complexity);
            break;
    }
    
    // Add some random walls for variety but fewer than before
    const extraWalls = Math.max(0, Math.floor(level / 5) - 2);
    for (let i = 0; i < extraWalls; i++) {
        let x = Math.floor(Math.random() * (GRID_WIDTH - 4)) + 2;
        let y = Math.floor(Math.random() * (GRID_HEIGHT - 4)) + 2;
        if (grid[y][x] === 0) {
            grid[y][x] = 1;
        }
    }
}

function generateFortressLayout(complexity) {
    // Create concentric rectangles
    const layers = Math.floor(Math.min(GRID_WIDTH, GRID_HEIGHT) / 6);
    for (let layer = 0; layer < layers; layer++) {
        const offset = layer * 3 + 2;
        if (offset >= GRID_WIDTH - 2 || offset >= GRID_HEIGHT - 2) break;
        
        // Draw fortress walls
        for (let x = offset; x < GRID_WIDTH - offset; x++) {
            grid[offset][x] = 1;
            grid[GRID_HEIGHT - offset - 1][x] = 1;
        }
        for (let y = offset; y < GRID_HEIGHT - offset; y++) {
            grid[y][offset] = 1;
            grid[y][GRID_WIDTH - offset - 1] = 1;
        }
        
        // Add gates
        const gateCount = Math.floor(complexity * 4) + 1;
        for (let g = 0; g < gateCount; g++) {
            const side = Math.floor(Math.random() * 4);
            switch (side) {
                case 0: grid[offset][offset + Math.floor(Math.random() * (GRID_WIDTH - 2 * offset))] = 0; break;
                case 1: grid[GRID_HEIGHT - offset - 1][offset + Math.floor(Math.random() * (GRID_WIDTH - 2 * offset))] = 0; break;
                case 2: grid[offset + Math.floor(Math.random() * (GRID_HEIGHT - 2 * offset))][offset] = 0; break;
                case 3: grid[offset + Math.floor(Math.random() * (GRID_HEIGHT - 2 * offset))][GRID_WIDTH - offset - 1] = 0; break;
            }
        }
    }
}

function generateLabyrinthLayout(complexity) {
    // Create a traditional labyrinth with winding paths
    for (let y = 2; y < GRID_HEIGHT - 2; y += 2) {
        for (let x = 2; x < GRID_WIDTH - 2; x += 2) {
            grid[y][x] = 1;
            
            // Add walls in random directions
            if (Math.random() < complexity) {
                const directions = [{x: 0, y: 1}, {x: 1, y: 0}, {x: 0, y: -1}, {x: -1, y: 0}];
                const dir = directions[Math.floor(Math.random() * directions.length)];
                const newX = x + dir.x;
                const newY = y + dir.y;
                if (newX > 0 && newX < GRID_WIDTH - 1 && newY > 0 && newY < GRID_HEIGHT - 1) {
                    grid[newY][newX] = 1;
                }
            }
        }
    }
}

function generateChamberLayout(complexity) {
    // Create distinct chambers connected by corridors
    const chamberCount = Math.floor(complexity * 6) + 3;
    const chambers = [];
    
    // Generate chambers
    for (let i = 0; i < chamberCount; i++) {
        const width = Math.floor(Math.random() * 5) + 3;
        const height = Math.floor(Math.random() * 4) + 3;
        const x = Math.floor(Math.random() * (GRID_WIDTH - width - 2)) + 1;
        const y = Math.floor(Math.random() * (GRID_HEIGHT - height - 2)) + 1;
        
        chambers.push({x, y, width, height});
        
        // Draw chamber walls
        for (let cy = y; cy < y + height; cy++) {
            for (let cx = x; cx < x + width; cx++) {
                if (cx === x || cx === x + width - 1 || cy === y || cy === y + height - 1) {
                    grid[cy][cx] = 1;
                }
            }
        }
        
        // Add entrance
        const side = Math.floor(Math.random() * 4);
        switch (side) {
            case 0: grid[y][x + Math.floor(width / 2)] = 0; break;
            case 1: grid[y + height - 1][x + Math.floor(width / 2)] = 0; break;
            case 2: grid[y + Math.floor(height / 2)][x] = 0; break;
            case 3: grid[y + Math.floor(height / 2)][x + width - 1] = 0; break;
        }
    }
    
    // Connect chambers with corridors
    for (let i = 0; i < chambers.length - 1; i++) {
        const chamber1 = chambers[i];
        const chamber2 = chambers[i + 1];
        createCorridor(
            chamber1.x + Math.floor(chamber1.width / 2),
            chamber1.y + Math.floor(chamber1.height / 2),
            chamber2.x + Math.floor(chamber2.width / 2),
            chamber2.y + Math.floor(chamber2.height / 2)
        );
    }
}

function generateSpiralLayout(complexity) {
    const centerX = Math.floor(GRID_WIDTH / 2);
    const centerY = Math.floor(GRID_HEIGHT / 2);
    const maxRadius = Math.min(centerX, centerY) - 2;
    
    let x = centerX;
    let y = centerY;
    let dx = 0;
    let dy = -1;
    
    for (let i = 0; i < maxRadius * maxRadius; i++) {
        if (x >= 1 && x < GRID_WIDTH - 1 && y >= 1 && y < GRID_HEIGHT - 1) {
            if (Math.random() < complexity) {
                grid[y][x] = 1;
            }
        }
        
        if (x === centerX + dx && y === centerY + dy || 
            x === centerX - dx && y === centerY + dy ||
            x === centerX - dx && y === centerY - dy ||
            x === centerX + dx && y === centerY - dy) {
            let temp = dx;
            dx = -dy;
            dy = temp;
        }
        
        x += dx;
        y += dy;
    }
}

function createCorridor(x1, y1, x2, y2) {
    let currentX = x1;
    let currentY = y1;
    
    // Move horizontally first
    while (currentX !== x2) {
        grid[currentY][currentX] = 0;
        currentX += currentX < x2 ? 1 : -1;
    }
    
    // Then move vertically
    while (currentY !== y2) {
        grid[currentY][currentX] = 0;
        currentY += currentY < y2 ? 1 : -1;
    }
}

function addSpecialFeatures(level) {
    // Add special level features every few levels
    if (level % 5 === 0) {
        // Add teleporters
        addTeleporters();
    }
    
    if (level % 3 === 0) {
        // Add bonus areas
        addBonusAreas();
    }
    
    if (level % 7 === 0) {
        // Add temporary safe zones
        addSafeZones();
    }
}

function addTeleporters() {
    // Add 2 teleporter pairs
    for (let i = 0; i < 2; i++) {
        let x1, y1, x2, y2;
        
        // Find two empty spots
        do {
            x1 = Math.floor(Math.random() * (GRID_WIDTH - 4)) + 2;
            y1 = Math.floor(Math.random() * (GRID_HEIGHT - 4)) + 2;
        } while (grid[y1][x1] !== 0);
        
        do {
            x2 = Math.floor(Math.random() * (GRID_WIDTH - 4)) + 2;
            y2 = Math.floor(Math.random() * (GRID_HEIGHT - 4)) + 2;
        } while (grid[y2][x2] !== 0 || (x2 === x1 && y2 === y1));
        
        grid[y1][x1] = 4; // Teleporter entrance
        grid[y2][x2] = 4; // Teleporter exit
    }
}

function addBonusAreas() {
    // Create small bonus rooms with extra dots
    const roomCount = Math.floor(Math.random() * 2) + 1;
    
    for (let r = 0; r < roomCount; r++) {
        const roomSize = 3;
        let x = Math.floor(Math.random() * (GRID_WIDTH - roomSize - 2)) + 1;
        let y = Math.floor(Math.random() * (GRID_HEIGHT - roomSize - 2)) + 1;
        
        // Clear the room
        for (let ry = y; ry < y + roomSize; ry++) {
            for (let rx = x; rx < x + roomSize; rx++) {
                grid[ry][rx] = 0;
            }
        }
        
        // Mark center as special bonus area
        grid[y + 1][x + 1] = 5; // Special bonus dot
    }
}

function addSafeZones() {
    // Add temporary safe zones where enemies move slower
    const safeZoneCount = Math.floor(Math.random() * 3) + 1;
    
    for (let s = 0; s < safeZoneCount; s++) {
        let x = Math.floor(Math.random() * (GRID_WIDTH - 6)) + 3;
        let y = Math.floor(Math.random() * (GRID_HEIGHT - 6)) + 3;
        
        if (grid[y][x] === 0) {
            grid[y][x] = 6; // Safe zone marker
        }
    }
}

function getCoordinatorMove(enemy) {
    // Coordinate with other enemies to surround player
    const nearbyEnemies = enemies.filter(e => 
        e.id !== enemy.id && 
        Math.abs(e.x - enemy.x) + Math.abs(e.y - enemy.y) < 8 &&
        !e.scared
    );
    
    if (nearbyEnemies.length > 0 && Math.random() < enemy.cooperationLevel) {
        // Calculate optimal positioning to trap player
        const targetPositions = getOptimalSurroundPositions(player.x, player.y);
        const myTargetPos = targetPositions[enemy.id % targetPositions.length];
        
        let path = findPath(enemy.x, enemy.y, myTargetPos.x, myTargetPos.y);
        if (path && path.length > 0) {
            let nextStep = path[0];
            return {
                x: nextStep.x - enemy.x,
                y: nextStep.y - enemy.y
            };
        }
    }
    
    return getAggressiveMove(enemy);
}

function getTrapperMove(enemy) {
    // Try to cut off player's escape routes
    const playerDirection = player.direction;
    if (playerDirection.x === 0 && playerDirection.y === 0) {
        return getPatrolMove(enemy);
    }
    
    // Predict where player will be and try to block their path
    const futureX = player.x + playerDirection.x * 5;
    const futureY = player.y + playerDirection.y * 5;
    
    // Find a position that blocks the predicted path
    const blockPositions = [];
    for (let i = 1; i <= 5; i++) {
        const blockX = player.x + playerDirection.x * i;
        const blockY = player.y + playerDirection.y * i;
        if (blockX > 0 && blockX < GRID_WIDTH - 1 && 
            blockY > 0 && blockY < GRID_HEIGHT - 1 &&
            grid[blockY][blockX] !== 1) {
            blockPositions.push({x: blockX, y: blockY});
        }
    }
    
    if (blockPositions.length > 0) {
        const targetPos = blockPositions[Math.floor(Math.random() * blockPositions.length)];
        let path = findPath(enemy.x, enemy.y, targetPos.x, targetPos.y);
        if (path && path.length > 0) {
            let nextStep = path[0];
            return {
                x: nextStep.x - enemy.x,
                y: nextStep.y - enemy.y
            };
        }
    }
    
    return getAmbushMove(enemy);
}

function getOptimalSurroundPositions(targetX, targetY) {
    // Calculate positions around the target for coordinated attack
    const positions = [];
    const radius = 3;
    
    for (let angle = 0; angle < 2 * Math.PI; angle += Math.PI / 4) {
        const x = Math.round(targetX + Math.cos(angle) * radius);
        const y = Math.round(targetY + Math.sin(angle) * radius);
        
        if (x > 0 && x < GRID_WIDTH - 1 && y > 0 && y < GRID_HEIGHT - 1 && grid[y][x] !== 1) {
            positions.push({x, y});
        }
    }
    
    return positions.length > 0 ? positions : [{x: targetX + 1, y: targetY}];
}

// Enhanced input handling with smooth controls
let keys = {};
let inputBuffer = [];

document.addEventListener('keydown', (e) => {
    keys[e.key] = true;
    
    // Buffer inputs for smoother gameplay
    if (['ArrowUp', 'ArrowDown', 'ArrowLeft', 'ArrowRight'].includes(e.key)) {
        inputBuffer.push(e.key);
        if (inputBuffer.length > 3) inputBuffer.shift();
    }
    
    // Immediate direction change for responsiveness
    if (e.key === 'ArrowUp') player.direction = { x: 0, y: -1 };
    else if (e.key === 'ArrowDown') player.direction = { x: 0, y: 1 };
    else if (e.key === 'ArrowLeft') player.direction = { x: -1, y: 0 };
    else if (e.key === 'ArrowRight') player.direction = { x: 1, y: 0 };
    
    // Pause functionality
    if (e.key === ' ' || e.key === 'Escape') {
        game.isPaused = !game.isPaused;
    }
});

document.addEventListener('keyup', (e) => {
    keys[e.key] = false;
});

// Enhanced game update with improved mechanics
function update() {
    if (!game.isPlaying || game.isPaused) return;
    
    // Update power pellet timer
    if (game.powerPelletActive) {
        game.powerPelletTimer--;
        if (game.powerPelletTimer <= 0) {
            game.powerPelletActive = false;
            enemies.forEach(enemy => {
                enemy.scared = false;
                enemy.scaredTimer = 0;
            });
        }
    }
    
    // Update player
    updatePlayer();
    
    // Update enemies with improved AI
    updateEnemies();
    
    // Use enhanced UI update
    updateUIEnhanced();
    
    // Strategic analysis in debug mode
    if (debugMode && Math.random() < 0.1) { // 10% chance per frame
        const strategy = calculateOptimalStrategy();
        console.log('Live Strategy:', strategy.recommendation);
    }
}

function updatePlayer() {
    player.moveTimer++;
    if (player.moveTimer >= game.playerSpeed) {
        player.moveTimer = 0;
        
        // Try buffered input for smoother controls
        let targetDirection = player.direction;
        for (let bufferedKey of inputBuffer) {
            let testDirection = { x: 0, y: 0 };
            if (bufferedKey === 'ArrowUp') testDirection = { x: 0, y: -1 };
            else if (bufferedKey === 'ArrowDown') testDirection = { x: 0, y: 1 };
            else if (bufferedKey === 'ArrowLeft') testDirection = { x: -1, y: 0 };
            else if (bufferedKey === 'ArrowRight') testDirection = { x: 1, y: 0 };
            
            let testX = player.x + testDirection.x;
            let testY = player.y + testDirection.y;
            
            if (grid[testY] && grid[testY][testX] !== 1) {
                targetDirection = testDirection;
                inputBuffer = inputBuffer.filter(key => key !== bufferedKey);
                break;
            }
        }
        
        let newX = player.x + targetDirection.x;
        let newY = player.y + targetDirection.y;
        
        if (grid[newY] && grid[newY][newX] !== 1) {
            player.x = newX;
            player.y = newY;
            player.direction = targetDirection;
            
            // Handle special tiles
            handleSpecialTiles(newX, newY);
            
            // Collect dots with combo system
            if (grid[newY][newX] === 2) {
                grid[newY][newX] = 0;
                
                // Combo system for strategic play
                let currentTime = Date.now();
                if (currentTime - game.lastDotTime < 1000) {
                    game.comboCounter++;
                } else {
                    game.comboCounter = 1;
                }
                game.lastDotTime = currentTime;
                
                let comboBonus = Math.min(game.comboCounter, 10);
                game.score += (10 + comboBonus) * game.multiplier;
                game.dotsCollected++;
                
                if (game.dotsCollected >= game.totalDots) {
                    nextLevel();
                }
            }
            
            // Collect power pellets
            if (grid[newY][newX] === 3) {
                grid[newY][newX] = 0;
                game.score += 50 * game.multiplier;
                game.powerPelletActive = true;
                game.powerPelletTimer = 400 + game.level * 20; // Longer duration at higher levels
                
                enemies.forEach(enemy => {
                    enemy.scared = true;
                    enemy.scaredTimer = game.powerPelletTimer;
                });
            }
            
            // Special bonus dots
            if (grid[newY][newX] === 5) {
                grid[newY][newX] = 0;
                game.score += 100 * game.multiplier;
                game.lives++; // Bonus life for special dots
            }
        }
    }
}

function handleSpecialTiles(x, y) {
    // Handle teleporters
    if (grid[y][x] === 4) {
        // Find the other teleporter
        for (let ty = 0; ty < GRID_HEIGHT; ty++) {
            for (let tx = 0; tx < GRID_WIDTH; tx++) {
                if (grid[ty][tx] === 4 && (tx !== x || ty !== y)) {
                    player.x = tx;
                    player.y = ty;
                    return;
                }
            }
        }
    }
    
    // Handle safe zones - temporary speed boost for player
    if (grid[y][x] === 6) {
        game.playerSpeed = Math.max(4, game.playerSpeed - 2);
        setTimeout(() => {
            game.playerSpeed = Math.min(game.basePlayerSpeed, game.playerSpeed + 2);
        }, 3000);
    }
}

function updateEnemies() {
    enemies.forEach((enemy, index) => {
        enemy.moveTimer++;
        enemy.personalityTimer++;
        
        if (enemy.scared) {
            enemy.scaredTimer--;
            if (enemy.scaredTimer <= 0) {
                enemy.scared = false;
            }
        }
        
        // Enemies move slower in safe zones
        let moveSpeed = enemy.scared ? game.enemySpeed * 1.5 : game.enemySpeed;
        if (grid[enemy.y] && grid[enemy.y][enemy.x] === 6) {
            moveSpeed *= 1.8; // Slower in safe zones
        }
        
        if (enemy.moveTimer >= moveSpeed) {
            enemy.moveTimer = 0;
            
            let move = getEnemyMove(enemy);
            if (move) {
                enemy.x += move.x;
                enemy.y += move.y;
                enemy.lastDirection = move;
            }
        }
        
        // Check collision with player
        if (enemy.x === player.x && enemy.y === player.y) {
            if (enemy.scared) {
                game.score += (200 + game.level * 50) * game.multiplier;
                enemy.x = GRID_WIDTH - 2;
                enemy.y = GRID_HEIGHT - 2;
                enemy.scared = false;
                enemy.scaredTimer = 0;
            } else {
                game.lives--;
                player.x = 1;
                player.y = 1;
                game.comboCounter = 0; // Reset combo on death
                
                if (game.lives <= 0) {
                    gameOver();
                }
            }
        }
    });
}

function getEnemyMove(enemy) {
    // Update enemy's knowledge of player position
    enemy.lastPlayerPosition = {x: player.x, y: player.y};
    
    if (enemy.scared) {
        // Run away from player with improved escape logic
        return getEnhancedRunAwayMove(enemy);
    }
    
    // Smart mode enemies use more sophisticated strategies
    if (enemy.smartMode && Math.random() < enemy.predictionAccuracy) {
        return getSmartEnemyMove(enemy);
    }
    
    switch (enemy.behavior) {
        case 'aggressive':
            return getAggressiveMove(enemy);
        case 'patrol':
            return getPatrolMove(enemy);
        case 'ambush':
            return getAmbushMove(enemy);
        case 'random':
            return getRandomMove(enemy);
        case 'coordinator':
            return getCoordinatorMove(enemy);
        case 'trapper':
            return getTrapperMove(enemy);
        default:
            return getAggressiveMove(enemy);
    }
}

function getSmartEnemyMove(enemy) {
    // Advanced AI that considers multiple factors
    const distanceToPlayer = Math.abs(enemy.x - player.x) + Math.abs(enemy.y - player.y);
    
    // Close range: direct pursuit
    if (distanceToPlayer <= 3) {
        return getAggressiveMove(enemy);
    }
    
    // Medium range: use prediction and coordination
    if (distanceToPlayer <= 8) {
        // Predict player movement
        const predictedX = player.x + player.direction.x * 2;
        const predictedY = player.y + player.direction.y * 2;
        
        // Clamp to grid bounds
        const clampedX = Math.max(1, Math.min(GRID_WIDTH - 2, predictedX));
        const clampedY = Math.max(1, Math.min(GRID_HEIGHT - 2, predictedY));
        
        let path = findPath(enemy.x, enemy.y, clampedX, clampedY);
        if (path && path.length > 0) {
            let nextStep = path[0];
            return {
                x: nextStep.x - enemy.x,
                y: nextStep.y - enemy.y
            };
        }
    }
    
    // Long range: patrol or coordinate
    return enemy.behavior === 'coordinator' ? getCoordinatorMove(enemy) : getPatrolMove(enemy);
}

function getEnhancedRunAwayMove(enemy) {
    let moves = [];
    let directions = [
        {x: 1, y: 0}, {x: -1, y: 0}, 
        {x: 0, y: 1}, {x: 0, y: -1}
    ];
    
    for (let dir of directions) {
        let newX = enemy.x + dir.x;
        let newY = enemy.y + dir.y;
        if (grid[newY] && grid[newY][newX] !== 1) {
            let distanceFromPlayer = Math.abs(newX - player.x) + Math.abs(newY - player.y);
            
            // Also consider distance from other enemies to avoid clustering
            let distanceFromOthers = 0;
            enemies.forEach(other => {
                if (other.id !== enemy.id) {
                    distanceFromOthers += Math.abs(newX - other.x) + Math.abs(newY - other.y);
                }
            });
            
            moves.push({
                move: dir, 
                distance: distanceFromPlayer,
                separation: distanceFromOthers
            });
        }
    }
    
    if (moves.length > 0) {
        // Choose move that maximizes distance from player and separates from other enemies
        moves.sort((a, b) => (b.distance + b.separation * 0.3) - (a.distance + a.separation * 0.3));
        return moves[0].move;
    }
    return null;
}

function getAggressiveMove(enemy) {
    // Use A* pathfinding for smart pursuit
    let path = findPath(enemy.x, enemy.y, player.x, player.y);
    if (path && path.length > 0) {
        let nextStep = path[0];
        return {
            x: nextStep.x - enemy.x,
            y: nextStep.y - enemy.y
        };
    }
    return getRandomMove(enemy);
}

function getPatrolMove(enemy) {
    // Patrol behavior with occasional aggressive moves
    if (enemy.personalityTimer % 120 < 60) {
        return getAggressiveMove(enemy);
    }
    
    if (!enemy.patrolTarget || (enemy.x === enemy.patrolTarget.x && enemy.y === enemy.patrolTarget.y)) {
        // Set new patrol target
        enemy.patrolTarget = {
            x: Math.floor(Math.random() * (GRID_WIDTH - 4)) + 2,
            y: Math.floor(Math.random() * (GRID_HEIGHT - 4)) + 2
        };
    }
    
    let path = findPath(enemy.x, enemy.y, enemy.patrolTarget.x, enemy.patrolTarget.y);
    if (path && path.length > 0) {
        let nextStep = path[0];
        return {
            x: nextStep.x - enemy.x,
            y: nextStep.y - enemy.y
        };
    }
    return getRandomMove(enemy);
}

function getAmbushMove(enemy) {
    // Try to intercept player's path
    let predictedX = player.x + player.direction.x * 3;
    let predictedY = player.y + player.direction.y * 3;
    
    // Clamp to grid bounds
    predictedX = Math.max(1, Math.min(GRID_WIDTH - 2, predictedX));
    predictedY = Math.max(1, Math.min(GRID_HEIGHT - 2, predictedY));
    
    let path = findPath(enemy.x, enemy.y, predictedX, predictedY);
    if (path && path.length > 0) {
        let nextStep = path[0];
        return {
            x: nextStep.x - enemy.x,
            y: nextStep.y - enemy.y
        };
    }
    return getAggressiveMove(enemy);
}

function getRandomMove(enemy) {
    let moves = [];
    let directions = [
        {x: 1, y: 0}, {x: -1, y: 0}, 
        {x: 0, y: 1}, {x: 0, y: -1}
    ];
    
    for (let dir of directions) {
        let newX = enemy.x + dir.x;
        let newY = enemy.y + dir.y;
        if (grid[newY] && grid[newY][newX] !== 1) {
            moves.push(dir);
        }
    }
    
    if (moves.length > 0) {
        return moves[Math.floor(Math.random() * moves.length)];
    }
    return null;
}

// Enhanced rendering with visual improvements and special effects
function render() {
    ctx.fillStyle = '#111';
    ctx.fillRect(0, 0, canvas.width, canvas.height);
    
    // Draw grid with improved visuals
    for (let y = 0; y < GRID_HEIGHT; y++) {
        for (let x = 0; x < GRID_WIDTH; x++) {
            if (grid[y][x] === 1) {
                // Walls with gradient effect
                let gradient = ctx.createLinearGradient(
                    x * CELL_SIZE, y * CELL_SIZE,
                    (x + 1) * CELL_SIZE, (y + 1) * CELL_SIZE
                );
                gradient.addColorStop(0, '#666');
                gradient.addColorStop(1, '#333');
                ctx.fillStyle = gradient;
                ctx.fillRect(x * CELL_SIZE, y * CELL_SIZE, CELL_SIZE, CELL_SIZE);
                
                // Wall border
                ctx.strokeStyle = '#888';
                ctx.lineWidth = 0.5;
                ctx.strokeRect(x * CELL_SIZE, y * CELL_SIZE, CELL_SIZE, CELL_SIZE);
            } else if (grid[y][x] === 2) {
                // Dots with glow effect
                ctx.fillStyle = '#fff';
                ctx.shadowColor = '#fff';
                ctx.shadowBlur = 3;
                ctx.beginPath();
                ctx.arc(x * CELL_SIZE + CELL_SIZE/2, y * CELL_SIZE + CELL_SIZE/2, 2, 0, Math.PI * 2);
                ctx.fill();
                ctx.shadowBlur = 0;
            } else if (grid[y][x] === 3) {
                // Power pellets with pulsing effect
                let pulse = Math.sin(Date.now() * 0.01) * 0.3 + 0.7;
                ctx.fillStyle = `rgba(255, 255, 0, ${pulse})`;
                ctx.shadowColor = '#ff0';
                ctx.shadowBlur = 8;
                ctx.beginPath();
                ctx.arc(x * CELL_SIZE + CELL_SIZE/2, y * CELL_SIZE + CELL_SIZE/2, 6, 0, Math.PI * 2);
                ctx.fill();
                ctx.shadowBlur = 0;
            } else if (grid[y][x] === 4) {
                // Teleporters with swirling effect
                let swirl = Date.now() * 0.005;
                ctx.fillStyle = `hsl(${swirl * 57.3}, 70%, 50%)`;
                ctx.shadowColor = ctx.fillStyle;
                ctx.shadowBlur = 6;
                ctx.beginPath();
                ctx.arc(x * CELL_SIZE + CELL_SIZE/2, y * CELL_SIZE + CELL_SIZE/2, 8, 0, Math.PI * 2);
                ctx.fill();
                ctx.shadowBlur = 0;
            } else if (grid[y][x] === 5) {
                // Special bonus dots with sparkle effect
                let sparkle = Math.sin(Date.now() * 0.02) * 0.4 + 0.6;
                ctx.fillStyle = `rgba(0, 255, 255, ${sparkle})`;
                ctx.shadowColor = '#0ff';
                ctx.shadowBlur = 10;
                ctx.beginPath();
                ctx.arc(x * CELL_SIZE + CELL_SIZE/2, y * CELL_SIZE + CELL_SIZE/2, 5, 0, Math.PI * 2);
                ctx.fill();
                ctx.shadowBlur = 0;
            } else if (grid[y][x] === 6) {
                // Safe zones with gentle green glow
                ctx.fillStyle = 'rgba(0, 255, 0, 0.2)';
                ctx.fillRect(x * CELL_SIZE, y * CELL_SIZE, CELL_SIZE, CELL_SIZE);
                ctx.strokeStyle = '#0f0';
                ctx.lineWidth = 1;
                ctx.strokeRect(x * CELL_SIZE, y * CELL_SIZE, CELL_SIZE, CELL_SIZE);
            }
        }
    }
    
    // Draw player with animation
    let playerPulse = Math.sin(Date.now() * 0.02) * 0.1 + 0.9;
    ctx.fillStyle = '#ff0';
    ctx.shadowColor = '#ff0';
    ctx.shadowBlur = 5;
    ctx.beginPath();
    ctx.arc(
        player.x * CELL_SIZE + CELL_SIZE/2, 
        player.y * CELL_SIZE + CELL_SIZE/2, 
        (CELL_SIZE/2 - 2) * playerPulse, 
        0, Math.PI * 2
    );
    ctx.fill();
    ctx.shadowBlur = 0;
    
    // Draw direction indicator
    if (player.direction.x !== 0 || player.direction.y !== 0) {
        ctx.fillStyle = '#fff';
        ctx.beginPath();
        ctx.arc(
            player.x * CELL_SIZE + CELL_SIZE/2 + player.direction.x * 6,
            player.y * CELL_SIZE + CELL_SIZE/2 + player.direction.y * 6,
            2, 0, Math.PI * 2
        );
        ctx.fill();
    }
    
    // Draw enemies with enhanced visuals
    enemies.forEach((enemy, index) => {
        if (enemy.scared) {
            // Scared enemies flash blue
            let flash = Math.sin(Date.now() * 0.03) > 0 ? '#00f' : '#006';
            ctx.fillStyle = flash;
            ctx.shadowColor = '#00f';
            ctx.shadowBlur = 4;
        } else {
            ctx.fillStyle = enemy.color;
            ctx.shadowColor = enemy.color;
            ctx.shadowBlur = 3;
        }
        
        // Enemy body with smart mode indicator
        if (enemy.smartMode) {
            ctx.shadowBlur = 8;
            ctx.strokeStyle = '#fff';
            ctx.lineWidth = 2;
            ctx.strokeRect(enemy.x * CELL_SIZE + 1, enemy.y * CELL_SIZE + 1, CELL_SIZE - 2, CELL_SIZE - 2);
        }
        
        ctx.fillRect(enemy.x * CELL_SIZE + 2, enemy.y * CELL_SIZE + 2, CELL_SIZE - 4, CELL_SIZE - 4);
        
        // Enemy eyes
        ctx.shadowBlur = 0;
        ctx.fillStyle = '#fff';
        ctx.fillRect(enemy.x * CELL_SIZE + 4, enemy.y * CELL_SIZE + 4, 3, 3);
        ctx.fillRect(enemy.x * CELL_SIZE + 11, enemy.y * CELL_SIZE + 4, 3, 3);
        
        ctx.fillStyle = '#000';
        ctx.fillRect(enemy.x * CELL_SIZE + 5, enemy.y * CELL_SIZE + 5, 1, 1);
        ctx.fillRect(enemy.x * CELL_SIZE + 12, enemy.y * CELL_SIZE + 5, 1, 1);
        
        // Behavior indicator
        ctx.fillStyle = '#fff';
        ctx.font = '8px monospace';
        ctx.textAlign = 'center';
        const behaviorText = enemy.behavior.charAt(0).toUpperCase();
        ctx.fillText(behaviorText, enemy.x * CELL_SIZE + CELL_SIZE/2, enemy.y * CELL_SIZE + CELL_SIZE - 2);
        ctx.textAlign = 'start';
    });
    
    // Draw power pellet timer
    if (game.powerPelletActive) {
        let timerPercent = game.powerPelletTimer / 400;
        ctx.fillStyle = `rgba(255, 255, 0, 0.3)`;
        ctx.fillRect(0, 0, canvas.width * timerPercent, 5);
    }
    
    // Draw pause indicator
    if (game.isPaused && game.isPlaying) {
        ctx.fillStyle = 'rgba(0, 0, 0, 0.8)';
        ctx.fillRect(0, 0, canvas.width, canvas.height);
        
        ctx.fillStyle = 'rgba(255, 255, 255, 0.9)';
        ctx.font = '32px monospace';
        ctx.textAlign = 'center';
        ctx.fillText('PAUSED', canvas.width / 2, canvas.height / 2);
        ctx.font = '16px monospace';
        ctx.fillText('Press SPACE to resume', canvas.width / 2, canvas.height / 2 + 40);
        ctx.textAlign = 'start';
    }
}

// Game loop
function gameLoop() {
    update();
    render();
    requestAnimationFrame(gameLoop);
}

// Enhanced UI updates with additional information
function updateUI() {
    document.getElementById('score').textContent = game.score.toLocaleString();
    document.getElementById('level').textContent = game.level;
    document.getElementById('lives').textContent = game.lives;
    document.getElementById('multiplier').textContent = game.multiplier + 'x';
    
    // Update combo counter display
    if (game.comboCounter > 1) {
        document.getElementById('combo').textContent = game.comboCounter + 'x Combo!';
        document.getElementById('combo').style.display = 'block';
    } else {
        document.getElementById('combo').style.display = 'none';
    }
    
    // Update dots remaining
    let dotsRemaining = game.totalDots - game.dotsCollected;
    document.getElementById('dots').textContent = dotsRemaining;
}

// Enhanced updateUI with performance stats and visual feedback
function updateUIEnhanced() {
    updateUI();
    
    // Update theme indicator
    const themes = ['Classic', 'Fortress', 'Labyrinth', 'Chambers', 'Spiral'];
    const themeIndex = Math.min(themes.length - 1, Math.floor((game.level - 1) / 3));
    document.getElementById('themeIndicator').textContent = `Theme: ${themes[themeIndex]}`;
    
    // Update performance stats
    performanceStats.frameCount++;
    const now = Date.now();
    if (now - performanceStats.lastFrameTime >= 1000) {
        performanceStats.fps = performanceStats.frameCount;
        performanceStats.frameCount = 0;
        performanceStats.lastFrameTime = now;
        
        document.getElementById('fpsCounter').textContent = performanceStats.fps;
        
        // Update cache hit rate
        const hitRate = cacheStats.hits + cacheStats.misses > 0 ? 
            Math.round(cacheStats.hits / (cacheStats.hits + cacheStats.misses) * 100) : 0;
        document.getElementById('cacheHitRate').textContent = hitRate + '%';
    }
    
    // Enhanced combo display
    const comboElement = document.getElementById('combo');
    if (game.comboCounter > 5) {
        comboElement.classList.add('mega-combo');
    } else {
        comboElement.classList.remove('mega-combo');
    }
    
    // Highlight score when it increases
    if (game.lastScore !== game.score) {
        document.querySelector('#score').parentElement.classList.add('highlight');
        setTimeout(() => {
            document.querySelector('#score').parentElement.classList.remove('highlight');
        }, 500);
        game.lastScore = game.score;
    }
}

// Game theory and strategic elements
function calculateOptimalStrategy() {
    // Analyze current game state for strategic recommendations
    const playerSafety = calculatePlayerSafety();
    const resourceDistribution = analyzeResourceDistribution();
    const enemyThreatLevel = calculateEnemyThreatLevel();
    
    return {
        safety: playerSafety,
        resources: resourceDistribution,
        threat: enemyThreatLevel,
        recommendation: getStrategicRecommendation(playerSafety, enemyThreatLevel)
    };
}

function calculatePlayerSafety() {
    let safePaths = 0;
    let totalPaths = 0;
    
    // Check escape routes from current position
    const directions = [{x: 1, y: 0}, {x: -1, y: 0}, {x: 0, y: 1}, {x: 0, y: -1}];
    
    directions.forEach(dir => {
        let distance = 0;
        let x = player.x;
        let y = player.y;
        
        // Check how far we can go in this direction
        while (distance < 5) {
            x += dir.x;
            y += dir.y;
            
            if (x <= 0 || x >= GRID_WIDTH - 1 || y <= 0 || y >= GRID_HEIGHT - 1 || grid[y][x] === 1) {
                break;
            }
            
            distance++;
            totalPaths++;
            
            // Check if any enemies are in this path
            let enemyInPath = enemies.some(enemy => 
                Math.abs(enemy.x - x) + Math.abs(enemy.y - y) <= 2 && !enemy.scared
            );
            
            if (!enemyInPath) {
                safePaths++;
            }
        }
    });
    
    return totalPaths > 0 ? safePaths / totalPaths : 0;
}

function analyzeResourceDistribution() {
    let dotsNearPlayer = 0;
    let pelletsNearPlayer = 0;
    let totalDots = 0;
    let totalPellets = 0;
    
    for (let y = 0; y < GRID_HEIGHT; y++) {
        for (let x = 0; x < GRID_WIDTH; x++) {
            const distance = Math.abs(x - player.x) + Math.abs(y - player.y);
            
            if (grid[y][x] === 2) {
                totalDots++;
                if (distance <= 5) dotsNearPlayer++;
            } else if (grid[y][x] === 3) {
                totalPellets++;
                if (distance <= 5) pelletsNearPlayer++;
            }
        }
    }
    
    return {
        dotsNearby: dotsNearPlayer,
        pelletsNearby: pelletsNearPlayer,
        totalDots,
        totalPellets
    };
}

function calculateEnemyThreatLevel() {
    let immediateThreats = 0;
    let nearbyThreats = 0;
    
    enemies.forEach(enemy => {
        if (enemy.scared) return;
        
        const distance = Math.abs(enemy.x - player.x) + Math.abs(enemy.y - player.y);
        
        if (distance <= 2) {
            immediateThreats++;
        } else if (distance <= 5) {
            nearbyThreats++;
        }
    });
    
    return {
        immediate: immediateThreats,
        nearby: nearbyThreats,
        total: immediateThreats + nearbyThreats
    };
}

function getStrategicRecommendation(safety, threatLevel) {
    if (threatLevel.immediate > 0 && safety < 0.3) {
        return "DANGER: Find power pellet or escape immediately!";
    } else if (game.powerPelletActive && threatLevel.total > 0) {
        return "OPPORTUNITY: Hunt enemies for bonus points!";
    } else if (game.comboCounter > 3) {
        return "COMBO: Keep collecting dots quickly!";
    } else if (safety > 0.7) {
        return "SAFE: Good positioning, continue collecting.";
    } else {
        return "CAUTION: Watch for enemy patterns.";
    }
}

// Debug mode toggle (press 'D' key)
let debugMode = false;

document.addEventListener('keydown', (e) => {
    if (e.key === 'd' || e.key === 'D') {
        debugMode = !debugMode;
        document.getElementById('performanceStats').style.display = debugMode ? 'block' : 'none';
        
        if (debugMode) {
            const strategy = calculateOptimalStrategy();
            console.log('Strategic Analysis:', strategy);
        }
    }
});

// Replace the original updateUI call in the update function
function update() {
    if (!game.isPlaying || game.isPaused) return;
    
    // Update power pellet timer
    if (game.powerPelletActive) {
        game.powerPelletTimer--;
        if (game.powerPelletTimer <= 0) {
            game.powerPelletActive = false;
            enemies.forEach(enemy => {
                enemy.scared = false;
                enemy.scaredTimer = 0;
            });
        }
    }
    
    // Update player
    updatePlayer();
    
    // Update enemies with improved AI
    updateEnemies();
    
    // Use enhanced UI update
    updateUIEnhanced();
    
    // Strategic analysis in debug mode
    if (debugMode && Math.random() < 0.1) { // 10% chance per frame
        const strategy = calculateOptimalStrategy();
        console.log('Live Strategy:', strategy.recommendation);
    }
}

// Initialize game
generateLevel(1);
updateUI();
gameLoop();
