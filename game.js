const canvas = document.getElementById('gameCanvas');
const ctx = canvas.getContext('2d');
const CELL_SIZE = 20;
const GRID_WIDTH = 30;
const GRID_HEIGHT = 20;

canvas.width = GRID_WIDTH * CELL_SIZE;
canvas.height = GRID_HEIGHT * CELL_SIZE;

// Game state
let game = {
    score: 0,
    level: 1,
    lives: 3,
    multiplier: 1,
    isPlaying: true,
    isPaused: false,
    playerSpeed: 4,
    enemySpeed: 2,
    dotsCollected: 0,
    totalDots: 0
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

// Procedural level generation
function generateLevel(level) {
    grid = Array(GRID_HEIGHT).fill().map(() => Array(GRID_WIDTH).fill(0));
    
    // Create border walls
    for (let y = 0; y < GRID_HEIGHT; y++) {
        for (let x = 0; x < GRID_WIDTH; x++) {
            if (x === 0 || x === GRID_WIDTH - 1 || y === 0 || y === GRID_HEIGHT - 1) {
                grid[y][x] = 1;
            }
        }
    }
    
    // Generate maze using recursive division
    divideChamber(1, 1, GRID_WIDTH - 2, GRID_HEIGHT - 2, level);
    
    // Place dots and count them
    game.totalDots = 0;
    for (let y = 1; y < GRID_HEIGHT - 1; y++) {
        for (let x = 1; x < GRID_WIDTH - 1; x++) {
            if (grid[y][x] === 0) {
                grid[y][x] = 2; // dot
                game.totalDots++;
            }
        }
    }
    
    // Place power pellets
    let powerPellets = Math.min(4, Math.floor(level / 3) + 1);
    for (let i = 0; i < powerPellets; i++) {
        let placed = false;
        while (!placed) {
            let x = Math.floor(Math.random() * (GRID_WIDTH - 2)) + 1;
            let y = Math.floor(Math.random() * (GRID_HEIGHT - 2)) + 1;
            if (grid[y][x] === 2) {
                grid[y][x] = 3; // power pellet
                placed = true;
            }
        }
    }
    
    // Clear starting position
    grid[1][1] = 2;
    player.x = 1;
    player.y = 1;
    
    // Generate enemies
    enemies = [];
    let enemyCount = Math.min(4, Math.floor(level / 2) + 1);
    for (let i = 0; i < enemyCount; i++) {
        enemies.push({
            x: GRID_WIDTH - 2,
            y: GRID_HEIGHT - 2,
            moveTimer: 0,
            color: `hsl(${i * 60}, 100%, 50%)`,
            scared: false,
            scaredTimer: 0
        });
    }
}

// Maze generation using recursive division
function divideChamber(x, y, width, height, level) {
    if (width < 4 || height < 4) return;
    
    let horizontal = width < height;
    
    if (horizontal) {
        let wallY = y + 2 + Math.floor(Math.random() * (height - 3));
        for (let wx = x; wx < x + width; wx++) {
            grid[wallY][wx] = 1;
        }
        let holeX = x + Math.floor(Math.random() * width);
        grid[wallY][holeX] = 0;
        
        if (Math.random() < 0.7 - level * 0.01) {
            divideChamber(x, y, width, wallY - y, level);
            divideChamber(x, wallY + 1, width, height - (wallY - y) - 1, level);
        }
    } else {
        let wallX = x + 2 + Math.floor(Math.random() * (width - 3));
        for (let wy = y; wy < y + height; wy++) {
            grid[wy][wallX] = 1;
        }
        let holeY = y + Math.floor(Math.random() * height);
        grid[holeY][wallX] = 0;
        
        if (Math.random() < 0.7 - level * 0.01) {
            divideChamber(x, y, wallX - x, height, level);
            divideChamber(wallX + 1, y, width - (wallX - x) - 1, height, level);
        }
    }
}

// Input handling
let keys = {};
document.addEventListener('keydown', (e) => {
    keys[e.key] = true;
    
    if (e.key === 'ArrowUp') player.direction = { x: 0, y: -1 };
    else if (e.key === 'ArrowDown') player.direction = { x: 0, y: 1 };
    else if (e.key === 'ArrowLeft') player.direction = { x: -1, y: 0 };
    else if (e.key === 'ArrowRight') player.direction = { x: 1, y: 0 };
});

document.addEventListener('keyup', (e) => {
    keys[e.key] = false;
});

// Update game
function update() {
    if (!game.isPlaying || game.isPaused) return;
    
    // Update player
    player.moveTimer++;
    if (player.moveTimer >= game.playerSpeed) {
        player.moveTimer = 0;
        let newX = player.x + player.direction.x;
        let newY = player.y + player.direction.y;
        
        if (grid[newY] && grid[newY][newX] !== 1) {
            player.x = newX;
            player.y = newY;
            
            // Collect dots
            if (grid[newY][newX] === 2) {
                grid[newY][newX] = 0;
                game.score += 10 * game.multiplier;
                game.dotsCollected++;
                
                if (game.dotsCollected >= game.totalDots) {
                    nextLevel();
                }
            }
            
            // Collect power pellets
            if (grid[newY][newX] === 3) {
                grid[newY][newX] = 0;
                game.score += 50 * game.multiplier;
                enemies.forEach(enemy => {
                    enemy.scared = true;
                    enemy.scaredTimer = 300;
                });
            }
        }
    }
    
    // Update enemies
    enemies.forEach((enemy, index) => {
        enemy.moveTimer++;
        
        if (enemy.scared) {
            enemy.scaredTimer--;
            if (enemy.scaredTimer <= 0) {
                enemy.scared = false;
            }
        }
        
        if (enemy.moveTimer >= (enemy.scared ? game.enemySpeed * 2 : game.enemySpeed)) {
            enemy.moveTimer = 0;
            
            // Simple AI: move towards player
            let dx = player.x - enemy.x;
            let dy = player.y - enemy.y;
            let moves = [];
            
            if (dx > 0 && grid[enemy.y][enemy.x + 1] !== 1) moves.push({ x: 1, y: 0 });
            if (dx < 0 && grid[enemy.y][enemy.x - 1] !== 1) moves.push({ x: -1, y: 0 });
            if (dy > 0 && grid[enemy.y + 1] && grid[enemy.y + 1][enemy.x] !== 1) moves.push({ x: 0, y: 1 });
            if (dy < 0 && grid[enemy.y - 1] && grid[enemy.y - 1][enemy.x] !== 1) moves.push({ x: 0, y: -1 });
            
            if (moves.length > 0) {
                let move = moves[Math.floor(Math.random() * moves.length)];
                enemy.x += move.x;
                enemy.y += move.y;
            }
        }
        
        // Check collision with player
        if (enemy.x === player.x && enemy.y === player.y) {
            if (enemy.scared) {
                game.score += 200 * game.multiplier;
                enemy.x = GRID_WIDTH - 2;
                enemy.y = GRID_HEIGHT - 2;
                enemy.scared = false;
            } else {
                game.lives--;
                player.x = 1;
                player.y = 1;
                
                if (game.lives <= 0) {
                    gameOver();
                }
            }
        }
    });
    
    updateUI();
}

// Render game
function render() {
    ctx.fillStyle = '#111';
    ctx.fillRect(0, 0, canvas.width, canvas.height);
    
    // Draw grid
    for (let y = 0; y < GRID_HEIGHT; y++) {
        for (let x = 0; x < GRID_WIDTH; x++) {
            if (grid[y][x] === 1) {
                ctx.fillStyle = '#444';
                ctx.fillRect(x * CELL_SIZE, y * CELL_SIZE, CELL_SIZE, CELL_SIZE);
            } else if (grid[y][x] === 2) {
                ctx.fillStyle = '#fff';
                ctx.beginPath();
                ctx.arc(x * CELL_SIZE + CELL_SIZE/2, y * CELL_SIZE + CELL_SIZE/2, 2, 0, Math.PI * 2);
                ctx.fill();
            } else if (grid[y][x] === 3) {
                ctx.fillStyle = '#ff0';
                ctx.beginPath();
                ctx.arc(x * CELL_SIZE + CELL_SIZE/2, y * CELL_SIZE + CELL_SIZE/2, 5, 0, Math.PI * 2);
                ctx.fill();
            }
        }
    }
    
    // Draw player
    ctx.fillStyle = '#ff0';
    ctx.beginPath();
    ctx.arc(player.x * CELL_SIZE + CELL_SIZE/2, player.y * CELL_SIZE + CELL_SIZE/2, CELL_SIZE/2 - 2, 0, Math.PI * 2);
    ctx.fill();
    
    // Draw enemies
    enemies.forEach(enemy => {
        ctx.fillStyle = enemy.scared ? '#00f' : enemy.color;
        ctx.fillRect(enemy.x * CELL_SIZE + 2, enemy.y * CELL_SIZE + 2, CELL_SIZE - 4, CELL_SIZE - 4);
    });
}

// Game loop
function gameLoop() {
    update();
    render();
    requestAnimationFrame(gameLoop);
}

// UI updates
function updateUI() {
    document.getElementById('score').textContent = game.score;
    document.getElementById('level').textContent = game.level;
    document.getElementById('lives').textContent = game.lives;
    document.getElementById('multiplier').textContent = game.multiplier + 'x';
}

// Next level
function nextLevel() {
    game.level++;
    game.dotsCollected = 0;
    game.isPaused = true;
    
    // Show upgrades
    document.getElementById('upgrades').style.display = 'block';
    
    // Update upgrade costs
    document.querySelectorAll('.upgrade-btn').forEach(btn => {
        let upgrade = btn.dataset.upgrade;
        let cost = upgrade === 'speed' ? 100 : upgrade === 'lives' ? 500 : 1000;
        btn.disabled = game.score < cost;
    });
}

// Upgrades
document.querySelectorAll('.upgrade-btn').forEach(btn => {
    btn.addEventListener('click', () => {
        let upgrade = btn.dataset.upgrade;
        let cost = upgrade === 'speed' ? 100 : upgrade === 'lives' ? 500 : 1000;
        
        if (game.score >= cost) {
            game.score -= cost;
            
            if (upgrade === 'speed') {
                game.playerSpeed = Math.max(1, game.playerSpeed - 1);
            } else if (upgrade === 'lives') {
                game.lives++;
            } else if (upgrade === 'multiplier') {
                game.multiplier *= 2;
            }
            
            updateUI();
        }
    });
});

// Continue after upgrades
document.getElementById('upgrades').addEventListener('click', (e) => {
    if (e.target.id === 'upgrades') {
        document.getElementById('upgrades').style.display = 'none';
        game.isPaused = false;
        generateLevel(game.level);
    }
});

// Game over
function gameOver() {
    game.isPlaying = false;
    document.getElementById('finalScore').textContent = game.score;
    document.getElementById('gameOver').style.display = 'block';
}

// Initialize game
generateLevel(1);
updateUI();
gameLoop();
