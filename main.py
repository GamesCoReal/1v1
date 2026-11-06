from __future__ import annotations

import json
import math
import socket
import time
import random
import re
from fractions import Fraction
from panda3d.core import TextNode

from ursina import *
from ursina.shaders import unlit_shader

# ============================================================
# INITIALIZATION
# ============================================================

app = Ursina()
window.title = "Local Network FPS"
window.color = color.black
window.fps_counter.enabled = True
window.exit_button.visible = False

window.fps_counter.enabled = False
window.entity_counter.enabled = False
window.collider_counter.enabled = False

BG_DARK = color.black
BG_PANEL = color.dark_gray
BG_BUTTON = color.gray
BG_HOVER = color.light_gray
BG_PRESSED = color.white
TEXT_MAIN = color.white
TEXT_MUTED = color.gray
BORDER_COLOR = color.dark_gray
ACCENT = color.blue
TAB = color.orange
TAB_ACCENT = color.magenta

PORT = 50555

# 1 world unit = 1 inch
INCHES_PER_MILE = 63360
SECONDS_PER_HOUR = 3600

MPH_TO_UNITS_PER_SECOND = INCHES_PER_MILE / SECONDS_PER_HOUR

Sky()


# ============================================================
# NETWORKING - 4 PLAYER LAN
# ============================================================

PORT = 50555
MAX_PLAYERS = 4

# Character customization (inches and pounds)
MIN_HEIGHT, MAX_HEIGHT = 46, 75
MIN_WEIGHT, MAX_WEIGHT = 75, 360
DEFAULT_HEIGHT, DEFAULT_WEIGHT = 69, 161
character_height = DEFAULT_HEIGHT
character_weight = DEFAULT_WEIGHT

net = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)

def reset_network_socket():
    global net

    try:
        net.close()
    except OSError:
        pass

    net = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    net.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    net.setsockopt(socket.SOL_SOCKET, socket.SO_BROADCAST, 1)
    net.setblocking(False)

net.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
net.setblocking(False)

net.setsockopt(socket.SOL_SOCKET, socket.SO_BROADCAST, 1)

discovered_games = {}
discovery_active = False
last_discovery = 0.0

is_host = False
player_number = 0
host_address = None
client_address = None

players = {}
player_entities = {}

session_started = False
network_ready = False
last_send = 0.0
last_heartbeat = 0.0
last_remote_packet = {}

local_state = {
    "x": 0.0,
    "z": 0.0,
    "yaw": 0.0,
    "pitch": 0.0,
    "name": "Player",
    "height": DEFAULT_HEIGHT,
    "weight": DEFAULT_WEIGHT,
}

start_x = 0.0
start_z = 0.0

# Temporary compatibility with the old two-player code.
remote_state = {
    "x": 10.0,
    "z": 0.0,
    "yaw": 0.0,
    "pitch": 0.0,
    "name": "Opponent",
}

def calculate_jump_height(height, weight):
    return 20 + 0.15 * (height - 68) - 0.025 * (weight - 160)

def calculate_character_width(height, weight):
    """User-selected body-width formula; result is in inches."""
    return 0.45 * ((float(height) ** 2) * float(weight)) ** (1 / 3)

def calculate_max_hp(weight, height):
    return round(100 + ((0.6 * (weight - 75) / 285) + (0.4 * (height - 46) / 29)) * 200)

def create_player_entity(player_id, state=None):
    if player_id < 1 or player_id > MAX_PLAYERS or player_id == player_number:
        return
    if player_id in player_entities:
        return

    state = state or {}
    height_in = clamp(float(state.get("height", DEFAULT_HEIGHT)), MIN_HEIGHT, MAX_HEIGHT)
    weight_lb = clamp(float(state.get("weight", DEFAULT_WEIGHT)), MIN_WEIGHT, MAX_WEIGHT)

    height = height_in
    body_width = calculate_character_width(height_in, weight_lb)

    # Body proportions
    head_h = height * 0.125
    neck_h = height * 0.035
    torso_h = height * 0.285
    pelvis_h = height * 0.105

    legs_h = height - head_h - neck_h - torso_h - pelvis_h

    leg_top = legs_h
    pelvis_y = leg_top + pelvis_h / 2
    torso_y = leg_top + pelvis_h + torso_h / 2
    neck_y = leg_top + pelvis_h + torso_h + neck_h / 2
    head_y = height - head_h / 2

    shoulder_y = leg_top + pelvis_h + torso_h * 0.88

    # Arm dimensions
    arm_len = height * 0.31
    upper_arm_len = arm_len * 0.52
    lower_arm_len = arm_len * 0.48

    arm_x = body_width * 0.78
    limb_w = max(body_width * 0.22, height * 0.035)
    leg_w = max(body_width * 0.30, height * 0.055)

    # Colors
    palette = [color.azure, 
                color.orange, 
                color.green, 
                color.violet]
    shirt = palette[player_id - 1]
    skin = color.peach
    pants = color.violet

    root = Entity(
        position=(0, 0, 0),
        rotation_y=float(state.get("yaw", 0))
    )

    # Invisible collision hitbox
    hitbox = Entity(
        parent=root,
        model="cube",
        position=(0, height / 2, 0),
        scale=(
            body_width * 2.0,
            height,
            body_width * 1.5
        ),
        collider="box",
        visible=False,
    )
    hitbox.is_remote_player = True

    def part(model, pos, scale, tint, parent=root):
        return Entity(
            parent=parent,
            model=model,
            position=pos,
            scale=scale,
            color=tint
        )

    parts = []

    # =====================================
    # LEGS: Two cubes connecting the feet
    # =====================================

    foot_h = height * 0.045

    for side in (-1, 1):
        x = side * leg_w * 0.62

        # Shoe
        parts.append(part(
            "cube",
            (x, foot_h / 2, height * 0.035),
            (leg_w * 1.05, foot_h, height * 0.13),
            color.black
        ))

        # Entire leg cube
        leg_cube_h = legs_h - foot_h

        parts.append(part(
            "cube",
            (x, foot_h + leg_cube_h / 2, 0),
            (leg_w, leg_cube_h, leg_w),
            pants
        ))

    # =====================================
    # PELVIS
    # =====================================

    parts.append(part(
        "cube",
        (0, pelvis_y, 0),
        (body_width * 1.15, pelvis_h, body_width * 0.78),
        pants
    ))

    # =====================================
    # TORSO: Cube extending up to the head
    # =====================================

    torso_full_h = torso_h + neck_h

    parts.append(part(
        "cube",
        (0, torso_y + neck_h / 2, 0),
        (body_width, torso_full_h, body_width * 0.62),
        shirt
    ))

    # =====================================
    # NECK AND HEAD
    # =====================================

    parts.append(part(
        "cube",
        (0, neck_y, 0),
        (height * 0.075, neck_h, height * 0.075),
        skin
    ))

    parts.append(part(
        "sphere",
        (0, head_y, 0),
        (height * 0.145, head_h, height * 0.135),
        skin
    ))

    # Ears and eyes
    for side in (-1, 1):
        parts.append(part(
            "sphere",
            (side * height * 0.075, head_y, 0),
            height * 0.035,
            skin
        ))

        parts.append(part(
            "sphere",
            (side * height * 0.032, head_y + head_h * 0.06, height * 0.061),
            height * 0.018,
            color.black
        ))

    # Mouth
    parts.append(part(
        "cube",
        (0, head_y - head_h * 0.16, height * 0.064),
        (height * 0.045, height * 0.012, height * 0.012),
        color.brown
    ))

    # =====================================
    # ARMS: One cube through all three circles
    # =====================================

    for side in (-1, 1):
        sx = side * arm_x

        # Shoulder circle
        parts.append(part(
            "sphere",
            (sx, shoulder_y, 0),
            limb_w * 1,
            shirt
        ))

        # Full arm cube
        arm_center_x = sx + side * limb_w * 0.2

        parts.append(part(
            "cube",
            (arm_center_x, shoulder_y - arm_len / 2, 0),
            (limb_w, arm_len, limb_w),
            skin
        ))

        # Elbow circle
        elbow_y = shoulder_y - upper_arm_len

        parts.append(part(
            "sphere",
            (sx + side * limb_w * 0.2, elbow_y, 0),
            limb_w * 0.8,
            skin
        ))

        # Hand circle
        parts.append(part(
            "sphere",
            (sx + side * limb_w * 0.3, shoulder_y - arm_len, 0),
            limb_w * 0.8,
            skin
        ))

    # =====================================
    # SAVE PLAYER
    # =====================================

    player_entities[player_id] = {
        "root": root,
        "parts": parts,
        "hitbox": hitbox,
        "dimensions": (height_in, weight_lb),
    }

    update_player_entity(player_id, state)

def update_player_entity(player_id, state):
    if player_id == player_number:
        return
    if player_id not in player_entities:
        create_player_entity(player_id, state)
    if player_id not in player_entities:
        return
    entity = player_entities[player_id]
    entity["root"].position = (float(state.get("x", 0)), 0, float(state.get("z", 0)))
    entity["root"].rotation_y = float(state.get("yaw", 0))

    # Rebuild only if dimensions changed, so all clients render the same body size.
    height = clamp(float(state.get("height", DEFAULT_HEIGHT)), MIN_HEIGHT, MAX_HEIGHT)
    weight = clamp(float(state.get("weight", DEFAULT_WEIGHT)), MIN_WEIGHT, MAX_WEIGHT)
    old_dims = entity.get("dimensions")
    if old_dims != (height, weight):
        position = entity["root"].position
        yaw_value = entity["root"].rotation_y
        destroy(entity["root"])
        del player_entities[player_id]
        create_player_entity(player_id, {**state, "x": position.x, "z": position.z, "yaw": yaw_value, "height": height, "weight": weight})
        player_entities[player_id]["dimensions"] = (height, weight)


def remove_player_entity(player_id):
    if player_id in player_entities:
        destroy(player_entities[player_id]["root"])
        del player_entities[player_id]


def send_packet(message, address=None):
    target = address if address is not None else host_address

    if target is None or not network_ready:
        return

    try:
        net.sendto(json.dumps(message).encode("utf-8"), target)
    except (OSError, TypeError):
        pass

def broadcast_packet(message):
    if not is_host:
        return

    for pid, info in players.items():
        if pid != player_number:
            send_packet(message, info["address"])

def start_host():
    global is_host, player_number, network_ready
    global session_started, start_x, discovery_active

    if network_ready:
        return

    # Release the temporary discovery socket.
    reset_network_socket()
    discovery_active = False

    try:
        net.bind(("", PORT))
    except OSError as error:
        print("Could not host:", error)
        return

    is_host = True
    player_number = 1
    network_ready = True
    session_started = False

    start_x = -10.0
    local_state["x"] = start_x
    local_state["name"] = player_name

    players.clear()
    players[1] = {
        "address": None,
        "name": player_name,
        "state": dict(local_state),
        "last_seen": time.time(),
    }

    print("Hosting LAN game on port", PORT)

def start_join(host_ip):
    global is_host, player_number, host_address
    global network_ready

    if network_ready:
        return

    try:
        net.bind(("", 0))
    except OSError as error:
        print("Could not start client:", error)
        return

    host_address = (host_ip, PORT)
    network_ready = True
    is_host = False

    send_packet({
        "type": "join",
        "name": player_name,
        "height": character_height,
        "weight": character_weight,
    })

    print("Requesting connection to", host_ip)


def handle_join_request(message, address):
    global next_player_id

    existing = None

    for pid, info in players.items():
        if info["address"] == address:
            existing = pid
            break

    if existing is not None:
        send_packet({
            "type": "accepted",
            "id": existing,
            "players": {
                str(pid): {
                    "name": p["name"],
                    "state": p["state"],
                }
                for pid, p in players.items()
            },
        }, address)
        return

    if len(players) >= MAX_PLAYERS:
        send_packet({
            "type": "rejected",
            "reason": "The game is full.",
        }, address)
        return

    used_ids = set(players.keys())
    player_id = next(
        pid for pid in range(2, MAX_PLAYERS + 1)
        if pid not in used_ids
    )

    players[player_id] = {
        "address": address,
        "name": str(message.get("name", f"Player {player_id}"))[:20],
        "state": {
            "x": 10.0 if player_id == 2 else 0.0,
            "z": 0.0,
            "yaw": 0.0,
            "pitch": 0.0,
            "name": str(message.get("name", f"Player {player_id}"))[:20],
            "height": clamp(float(message.get("height", DEFAULT_HEIGHT)), MIN_HEIGHT, MAX_HEIGHT),
            "weight": clamp(float(message.get("weight", DEFAULT_WEIGHT)), MIN_WEIGHT, MAX_WEIGHT),
        },
        "last_seen": time.time(),
    }

    print(f"Player {player_id} joined from {address[0]}")

    send_packet({
        "type": "accepted",
        "id": player_id,
        "players": {
            str(pid): {
                "name": p["name"],
                "state": p["state"],
            }
            for pid, p in players.items()
        },
    }, address)

    broadcast_packet({
        "type": "roster",
        "players": {
            str(pid): {
                "name": p["name"],
                "state": p["state"],
            }
            for pid, p in players.items()
        },
    })

def process_network():
    global player_number, remote_state, last_remote_packet
    global menu_screen, menu_open
    global session_started
    global local_respawn_at, remote_respawn_at

    if not network_ready and not discovery_active:
        return

    for _ in range(100):
        try:
            data, address = net.recvfrom(8192)
        except BlockingIOError:
            break
        except OSError:
            break

        try:
            message = json.loads(data.decode("utf-8"))
        except (ValueError, UnicodeDecodeError):
            continue

        kind = message.get("type")

        # ====================================================
        # HOST: RESPOND TO GAME DISCOVERY
        # ====================================================

        if is_host and kind == "discover":
            send_packet({
                "type": "host_found",
                "host_name": players.get(1, {}).get("name", "Host"),
                "player_count": len(players),
                "max_players": MAX_PLAYERS,
            }, address)
            continue

        # ====================================================
        # HOST: RECEIVE CLIENT MESSAGES
        # ====================================================

        if is_host:

            if kind == "join":
                handle_join_request(message, address)

            elif kind == "leave":
                leaving_id = None

                for pid, info in list(players.items()):
                    if info["address"] == address:
                        leaving_id = pid
                        break

                if leaving_id is not None:
                    players.pop(leaving_id, None)
                    remove_player_entity(leaving_id)

                    broadcast_packet({
                        "type": "player_left",
                        "player": leaving_id,
                    })

            elif kind == "heartbeat":
                for pid, info in players.items():
                    if info["address"] == address:
                        info["last_seen"] = time.time()
                        break

            elif kind == "state":
                for pid, info in players.items():
                    if info["address"] == address:
                        info["state"].update(message.get("state", {}))
                        info["last_seen"] = time.time()

                        update_player_entity(pid, info["state"])
                        break

            elif kind == "shot":
                shooter_id = None

                for pid, info in players.items():
                    if info["address"] == address:
                        shooter_id = pid
                        break

                if shooter_id is not None:
                    message["shooter"] = shooter_id
                    process_remote_shot(message)
                    broadcast_packet(message)

            # --------------------------------------------
            # HEALTH UPDATE
            # --------------------------------------------

            elif kind == "health":
                for pid, info in players.items():
                    if info["address"] == address:

                        state = info["state"]

                        max_hp = calculate_max_hp(
                            state.get("weight", DEFAULT_WEIGHT),
                            state.get("height", DEFAULT_HEIGHT),
                        )

                        health = max(
                            0,
                            min(
                                max_hp,
                                int(message.get("health", max_hp))
                            )
                        )

                        info["health"] = health

                        broadcast_packet({
                            "type": "health",
                            "player": pid,
                            "health": health,
                        })

                        break

            # --------------------------------------------
            # RESPAWN UPDATE
            # --------------------------------------------

            elif kind == "respawn":
                for pid, info in players.items():
                    if info["address"] == address:

                        info["state"]["x"] = message.get("x", 0)
                        info["state"]["z"] = message.get("z", 0)

                        state = info["state"]

                        max_hp = calculate_max_hp(
                            state.get("weight", DEFAULT_WEIGHT),
                            state.get("height", DEFAULT_HEIGHT),
                        )

                        info["health"] = max_hp

                        broadcast_packet({
                            "type": "health",
                            "player": pid,
                            "health": max_hp,
                        })

                        broadcast_packet({
                            "type": "respawn",
                            "player": pid,
                            "x": message.get("x", 0),
                            "z": message.get("z", 0),
                        })

                        break

        # ====================================================
        # CLIENT: RECEIVE HOST MESSAGES
        # ====================================================

        else:

            # --------------------------------------------
            # DISCOVERY
            # --------------------------------------------

            if kind == "host_found" and discovery_active:
                discovered_games[address] = {
                    "name": message.get("host_name", "Host"),
                    "count": message.get("player_count", 1),
                    "max": message.get("max_players", MAX_PLAYERS),
                }
                continue

            if address != host_address:
                continue

            # --------------------------------------------
            # ACCEPTED
            # --------------------------------------------

            if kind == "accepted":
                player_number = int(message["id"])

                print(
                    "Connected! Your player ID is",
                    player_number
                )

                for pid, info in message.get("players", {}).items():
                    pid = int(pid)

                    if pid == player_number:
                        continue

                    players[pid] = {
                        "address": None,
                        "name": info["name"],
                        "state": info["state"],
                        "health": calculate_max_hp(
                            info["state"].get("weight", DEFAULT_WEIGHT),
                            info["state"].get("height", DEFAULT_HEIGHT),
                        ),
                        "last_seen": time.time(),
                    }

                    update_player_entity(pid, info["state"])

                open_client_lobby()

            # --------------------------------------------
            # REJECTED
            # --------------------------------------------

            elif kind == "rejected":
                reason = message.get(
                    "reason",
                    "Connection rejected"
                )

                print(reason)
                join_hint.text = reason

            # --------------------------------------------
            # MATCH START
            # --------------------------------------------

            elif kind == "match_start":
                begin_match()

            # --------------------------------------------
            # ROSTER UPDATE
            # --------------------------------------------

            elif kind == "roster":
                for pid, info in message.get("players", {}).items():
                    pid = int(pid)

                    if pid == player_number:
                        continue

                    players[pid] = {
                        "address": None,
                        "name": info["name"],
                        "state": info["state"],
                        "health": calculate_max_hp(
                            info["state"].get("weight", DEFAULT_WEIGHT),
                            info["state"].get("height", DEFAULT_HEIGHT),
                        ),
                        "last_seen": time.time(),
                    }

                    update_player_entity(pid, info["state"])

            # --------------------------------------------
            # PLAYER POSITION SNAPSHOT
            # --------------------------------------------

            elif kind == "snapshot":
                for pid, state in message.get("players", {}).items():
                    pid = int(pid)

                    if pid == player_number:
                        continue

                    if pid not in players:
                        players[pid] = {
                            "address": None,
                            "name": state.get("name", "Player"),
                            "state": state,
                            "health": calculate_max_hp(
                                state.get("weight", DEFAULT_WEIGHT),
                                state.get("height", DEFAULT_HEIGHT),
                            ),
                            "last_seen": time.time(),
                        }

                    players[pid]["state"].update(state)

                    update_player_entity(pid, state)

                    last_remote_packet[pid] = time.time()

            # --------------------------------------------
            # SHOT
            # --------------------------------------------

            elif kind == "shot":
                shooter_id = int(message.get("shooter", 0))

                if shooter_id != player_number:
                    process_remote_shot(message)

            # --------------------------------------------
            # HEALTH
            # --------------------------------------------

            elif kind == "health":
                pid = int(message.get("player", 0))

                if pid != player_number and pid in players:

                    state = players[pid]["state"]

                    max_hp = calculate_max_hp(
                        state.get("weight", DEFAULT_WEIGHT),
                        state.get("height", DEFAULT_HEIGHT),
                    )

                    players[pid]["health"] = max(
                        0,
                        min(
                            max_hp,
                            int(message.get("health", max_hp))
                        )
                    )

                    update_health_ui()

            # --------------------------------------------
            # RESPAWN
            # --------------------------------------------

            elif kind == "respawn":
                pid = int(message.get("player", 0))

                if pid != player_number and pid in players:

                    players[pid]["state"]["x"] = message.get("x", 0)
                    players[pid]["state"]["z"] = message.get("z", 0)

                    update_player_entity(
                        pid,
                        players[pid]["state"]
                    )

def network_update():
    global last_send, last_heartbeat

    if not network_ready or player_number == 0:
        return

    now = time.time()

    if discovery_active and now - last_discovery >= 1.0:
        send_game_discovery()
        last_discovery = now
        
    local_state["name"] = player_name
    local_state["height"] = character_height
    local_state["weight"] = character_weight
    local_state["x"] = float(local_body.x)
    local_state["z"] = float(local_body.z)
    local_state["yaw"] = float(yaw)
    local_state["pitch"] = float(pitch)

    if now - last_send >= 0.04:
        if is_host:
            players[1]["state"] = dict(local_state)

            snapshot = {
                str(pid): info["state"]
                for pid, info in players.items()
            }

            broadcast_packet({
                "type": "snapshot",
                "players": snapshot,
            })

        else:
            send_packet({
                "type": "state",
                "state": local_state,
            })

        last_send = now

    if not is_host and now - last_heartbeat >= 1.0:
        send_packet({"type": "heartbeat"})
        last_heartbeat = now


def start_game_search():
    global discovery_active, last_discovery

    if network_ready:
        return

    try:
        net.bind(("", 0))
    except OSError as error:
        print("Could not start game search:", error)
        return

    discovery_active = True
    last_discovery = 0.0
    print("Searching for LAN games...")


def send_game_discovery():
    try:
        net.sendto(
            json.dumps({"type": "discover"}).encode("utf-8"),
            ("255.255.255.255", PORT),
        )
    except OSError:
        pass

def connect_to_discovered_game(address):
    global host_address, network_ready, is_host, discovery_active

    if not discovery_active:
        return

    host_address = address
    is_host = False
    network_ready = True
    discovery_active = False

    send_packet({
        "type": "join",
        "name": player_name,
        "height": character_height,
        "weight": character_weight,
    })

    print("Joining game at", address[0])
    
# ============================================================
# GENERATED ARENA (ALL DIMENSIONS IN INCHES)
# ============================================================

WALL_HEIGHT = 120
WALL_THICKNESS = 36

CELL_SIZE = 36

MIN_MAP_SIZE = 30
MAX_MAP_SIZE = 60

EMPTY = " "
WALL = "w"
COVER = "c"

# Generated arena data
arena_grid = []
arena_width = 0
arena_depth = 0

ARENA_SIZE_X = 0
ARENA_SIZE_Z = 0
ARENA_HALF_X = 0
ARENA_HALF_Z = 0

# Compatibility with existing code
ARENA_SIZE = 0
ARENA_HALF = 0

arena_entities = []
cover_entities = []

# The host's generated map, shared with all joining players.
generated_map_data = None


# ============================================================
# MAP GENERATION
# ============================================================

def generate_map(seed: int) -> dict:
    rng = random.Random(int(seed))

    # Generate map dimensions.
    width = rng.randint(MIN_MAP_SIZE, MAX_MAP_SIZE)
    depth = rng.randint(MIN_MAP_SIZE, MAX_MAP_SIZE)

    area = width * depth

    # Determine original cover count.
    if area <= 1600:
        initial_count = 5
    elif area <= 2800:
        initial_count = 6
    else:
        initial_count = 7

    # Create empty grid.
    grid = [[EMPTY for _ in range(width)] for _ in range(depth)]

    # Create perimeter walls.
    for x in range(width):
        grid[0][x] = WALL
        grid[depth - 1][x] = WALL

    for z in range(depth):
        grid[z][0] = WALL
        grid[z][width - 1] = WALL

    # Track occupied cells.
    occupied = {
        (x, z)
        for z in range(depth)
        for x in range(width)
        if grid[z][x] == WALL
    }

    covers = []

    # --------------------------------------------------------
    # Place a cover.
    # --------------------------------------------------------

    def place_cover(x, z):
        position = (x, z)

        # Never overlap an existing object.
        if position in occupied:
            return False

        # Generate a deterministic random height.
        height = rng.uniform(
            CROUCH_EYE_HEIGHT,
            character_height
        ) + 5

        grid[z][x] = COVER
        occupied.add(position)

        covers.append({
            "position": position,
            "height": height,
        })

        return True

    # --------------------------------------------------------
    # Place the original 5–7 covers.
    # --------------------------------------------------------

    attempts = 0

    while len(covers) < initial_count and attempts < 50000:
        attempts += 1

        x = rng.randint(1, width - 2)
        z = rng.randint(1, depth - 2)

        place_cover(x, z)

    if len(covers) != initial_count:
        raise RuntimeError("Could not place all initial covers.")

    # --------------------------------------------------------
    # Give each original cover a 5% chance to spawn one
    # additional cover in one of its four directions.
    # --------------------------------------------------------

    original_covers = list(covers)

    directions = [
        (0, -1),   # North
        (0, 1),    # South
        (1, 0),    # East
        (-1, 0),   # West
    ]

    for cover in original_covers:

        if rng.random() >= 0.05:
            continue

        x, z = cover["position"]

        available_directions = list(directions)
        rng.shuffle(available_directions)

        for dx, dz in available_directions:
            nx = x + dx
            nz = z + dz

            # Brother covers must remain inside the walls.
            if not (0 < nx < width - 1 and 0 < nz < depth - 1):
                continue

            # Place the brother if its cell is available.
            if place_cover(nx, nz):
                break

    # --------------------------------------------------------
    # Return the completed map.
    # --------------------------------------------------------

    return {
        "seed": int(seed),
        "width": width,
        "depth": depth,
        "cell_size_inches": CELL_SIZE,
        "initial_cover_count": initial_count,
        "total_cover_count": len(covers),
        "grid": ["".join(row) for row in grid],
        "covers": covers,
    }


# ============================================================
# MAP VALIDATION
# ============================================================

def grid_to_string(grid):
    return "\n".join(grid)


def validate_map(map_data):
    grid = map_data["grid"]

    if len(grid) != map_data["depth"]:
        raise ValueError("Incorrect map depth.")

    if any(len(row) != map_data["width"] for row in grid):
        raise ValueError("Map rows have inconsistent widths.")

    allowed = {
        EMPTY,
        WALL,
        COVER,
    }

    for row in grid:
        for cell in row:
            if cell not in allowed:
                raise ValueError(f"Unknown map symbol: {cell!r}")

    # Check top and bottom walls.
    for x in range(map_data["width"]):
        if grid[0][x] != WALL or grid[-1][x] != WALL:
            raise ValueError("Missing perimeter wall.")

    # Check left and right walls.
    for z in range(map_data["depth"]):
        if grid[z][0] != WALL or grid[z][-1] != WALL:
            raise ValueError("Missing perimeter wall.")

    return True


# ============================================================
# BUILD ARENA
# ============================================================

def build_arena(seed_or_map):
    global arena_grid
    global arena_width, arena_depth
    global ARENA_SIZE_X, ARENA_SIZE_Z
    global ARENA_HALF_X, ARENA_HALF_Z
    global ARENA_SIZE, ARENA_HALF
    global arena_entities, cover_entities
    global generated_map_data

    # Remove previous arena objects.
    for entity in arena_entities:
        destroy(entity)

    arena_entities = []
    cover_entities = []

    # Use an already-generated map if one was supplied.
    # Otherwise, generate a new map from the seed.
    if isinstance(seed_or_map, dict):
        map_data = seed_or_map
    else:
        map_data = generate_map(seed_or_map)

    validate_map(map_data)

    generated_map_data = map_data

    arena_grid = map_data["grid"]
    arena_width = map_data["width"]
    arena_depth = map_data["depth"]

    # Calculate arena dimensions.
    ARENA_SIZE_X = arena_width * CELL_SIZE
    ARENA_SIZE_Z = arena_depth * CELL_SIZE

    ARENA_HALF_X = ARENA_SIZE_X / 2
    ARENA_HALF_Z = ARENA_SIZE_Z / 2

    ARENA_SIZE = max(ARENA_SIZE_X, ARENA_SIZE_Z)
    ARENA_HALF = ARENA_SIZE / 2

    # --------------------------------------------------------
    # Create floor.
    # --------------------------------------------------------

    floor = Entity(
        model="cube",
        position=(0, -6, 0),
        scale=(ARENA_SIZE_X, 12, ARENA_SIZE_Z),
        color=color.red,
        collider="box",
    )

    arena_entities.append(floor)

    # --------------------------------------------------------
    # Convert grid coordinates into world coordinates.
    # --------------------------------------------------------

    def cell_position(x, z):
        world_x = (x - (arena_width - 1) / 2) * CELL_SIZE
        world_z = (z - (arena_depth - 1) / 2) * CELL_SIZE

        return world_x, world_z

    # --------------------------------------------------------
    # Create perimeter walls.
    # --------------------------------------------------------

    for z, row in enumerate(arena_grid):
        for x, symbol in enumerate(row):

            if symbol != WALL:
                continue

            world_x, world_z = cell_position(x, z)

            entity = Entity(
                model="cube",
                position=(
                    world_x,
                    WALL_HEIGHT / 2,
                    world_z
                ),
                scale=(
                    CELL_SIZE,
                    WALL_HEIGHT,
                    CELL_SIZE
                ),
                color=color.blue,
                collider="box",
            )

            arena_entities.append(entity)

    # --------------------------------------------------------
    # Create covers using their saved individual heights.
    # --------------------------------------------------------

    for cover in map_data["covers"]:
        x, z = cover["position"]
        height = cover["height"]

        world_x, world_z = cell_position(x, z)

        entity = Entity(
            model="cube",
            position=(
                world_x,
                height / 2,
                world_z
            ),
            scale=(
                CELL_SIZE,
                height,
                CELL_SIZE
            ),
            color=color.yellow,
            collider="box",
        )

        arena_entities.append(entity)
        cover_entities.append(entity)

    return map_data


# ============================================================
# POSITION COLLISION
# ============================================================

def position_blocked(x, z):
    half_x = calculate_character_width(
        character_height,
        character_weight
    )

    half_z = half_x * 0.75

    # Arena boundaries.
    if (
        x - half_x < -ARENA_HALF_X + WALL_THICKNESS / 2
        or x + half_x > ARENA_HALF_X - WALL_THICKNESS / 2
        or z - half_z < -ARENA_HALF_Z + WALL_THICKNESS / 2
        or z + half_z > ARENA_HALF_Z - WALL_THICKNESS / 2
    ):
        return True

    # Cover collisions.
    for obstacle in cover_entities:
        if (
            x + half_x > obstacle.x - obstacle.scale_x / 2
            and x - half_x < obstacle.x + obstacle.scale_x / 2
            and z + half_z > obstacle.z - obstacle.scale_z / 2
            and z - half_z < obstacle.z + obstacle.scale_z / 2
        ):
            return True

    return False


# ============================================================
# SPAWN VALIDATION
# ============================================================

def is_spawn_position_valid(x, z, player_height, player_width):
    half_width = player_width

    player_min_x = x - half_width
    player_max_x = x + half_width
    player_min_z = z - half_width * 0.75
    player_max_z = z + half_width * 0.75

    # Arena boundaries.
    if (
        player_min_x < -ARENA_HALF_X + WALL_THICKNESS
        or player_max_x > ARENA_HALF_X - WALL_THICKNESS
        or player_min_z < -ARENA_HALF_Z + WALL_THICKNESS
        or player_max_z > ARENA_HALF_Z - WALL_THICKNESS
    ):
        return False

    # Generated cover collisions.
    for obstacle in cover_entities:
        cover_min_x = obstacle.x - obstacle.scale_x / 2
        cover_max_x = obstacle.x + obstacle.scale_x / 2
        cover_min_z = obstacle.z - obstacle.scale_z / 2
        cover_max_z = obstacle.z + obstacle.scale_z / 2

        if (
            player_max_x > cover_min_x
            and player_min_x < cover_max_x
            and player_max_z > cover_min_z
            and player_min_z < cover_max_z
        ):
            return False

    return True


# ============================================================
# FIND VALID SPAWN
# ============================================================

def find_valid_spawn(player_height, player_weight):
    player_width = calculate_character_width(
        player_height,
        player_weight
    )

    for _ in range(1000):
        x = random.uniform(
            -ARENA_HALF_X + 100,
            ARENA_HALF_X - 100
        )

        z = random.uniform(
            -ARENA_HALF_Z + 100,
            ARENA_HALF_Z - 100
        )

        if is_spawn_position_valid(
            x, z, player_height, player_width
        ):
            return x, z

    raise RuntimeError("Could not find a valid spawn position!")

# ============================================================
# PLAYERS
# ============================================================

def calculate_walking_speed_mph(height, weight):
    return (1031 * height) / (70 * weight)

def calculate_movement_speed(height, weight, mode="walk"):
    speed = calculate_walking_speed_mph(height, weight)

    if mode == "sprint":
        speed *= 1.5
    elif mode == "crouch":
        speed /= 2

    return speed * MPH_TO_UNITS_PER_SECOND

PLAYER_HEIGHT = character_height
STAND_EYE_HEIGHT = character_height * 0.88
CROUCH_EYE_HEIGHT = character_height * 0.45
MAX_HEALTH = calculate_max_hp(character_weight, character_height)

remote_body = Entity(
    enabled=False,
    model="cube",
    position=(remote_state["x"], PLAYER_HEIGHT / 2, remote_state["z"]),
    scale=(0.7, PLAYER_HEIGHT, 0.7),
    color=color.orange if is_host else color.azure,
    collider="box",
)
remote_body.is_remote_player = True

remote_head = Entity(
    enabled=False,
    model="sphere",
    position=(remote_state["x"], PLAYER_HEIGHT + 0.05, remote_state["z"]),
    scale=0.35,
    color=TAB_ACCENT,
    collider="sphere",
)
remote_head.is_remote_player = True

local_body = Entity(
    model="cube",
    position=(start_x, character_height / 2, 0),
    scale=(
        calculate_character_width(character_height, character_weight) * 2.0,
        character_height,
        calculate_character_width(character_height, character_weight) * 1.5,
    ),
    collider="box",
    visible=False,
)
local_body.is_player_body = True


def update_local_hitbox():
    width = calculate_character_width(
        character_height,
        character_weight,
    )

    height = character_height

    local_body.scale = (
        width * 2.0,
        height,
        width * 1.5,
    )

    local_body.y = height / 2

# ============================================================
# CAMERA AND GUN
# ============================================================

camera.position = (start_x, STAND_EYE_HEIGHT, 0)
camera.rotation = (0, local_state["yaw"], 0)
camera.fov = 90

mouse.locked = False
mouse.visible = True

gun = Entity(
    parent=camera,
    model="cube",
    position=(0.32, -100, 0.65),
    scale=(0.16, 0.16, 0.65),
    color=color.dark_gray,
)

# ============================================================
# WEAPONS, DAMAGE, BULLETS, RETICLE
# ============================================================

PRIMARY_WEAPONS = [
    {"name":"Pistol",  "id":"pistol",  "image": "assets/primary_weapons/pistol.png", "damage_per_bullet":25, "bullets_per_shot":1,  "bullet_formation":"single", "spread":0, "bullet_speed":120, "fire_rate":0.01, "magazine_size":12, "reload_type":"full",   "reload_time":1.2, "recoil":"", "fire_mode":"click"},
    {"name":"Shotgun", "id":"shotgun", "image": "assets/primary_weapons/shotgun.png","damage_per_bullet":10, "bullets_per_shot":11, "bullet_formation":"spread", "spread":2, "bullet_speed":100, "fire_rate":0.8,  "magazine_size":8 , "reload_type":"single", "reload_time":0.5, "recoil":"", "fire_mode":"click"},
    {"name":"Sniper",  "id":"sniper",  "image": "assets/primary_weapons/sniper.png", "damage_per_bullet":75, "bullets_per_shot":1,  "bullet_formation":"single", "spread":0, "bullet_speed":180, "fire_rate":1.2,  "magazine_size":5,  "reload_type":"full",   "reload_time":2.8, "recoil":"", "fire_mode":"click"},
    {"name":"AR",      "id":"ak",      "image": "assets/primary_weapons/ak.png",     "damage_per_bullet":20, "bullets_per_shot":1,  "bullet_formation":"single", "spread":0, "bullet_speed":120, "fire_rate":0.5,  "magazine_size":30, "reload_type":"full",   "reload_time":2.0, "recoil":"", "fire_mode":"automatic"},
]

# Internal lookup keeps existing HUD and network code compatible.
WEAPONS = {
    w["id"]: {
        "name": w["name"], "damage": w["damage_per_bullet"],
        "mode": w["fire_mode"], "bullets": w["bullets_per_shot"],
        "spread": w["spread"], "speed": w["bullet_speed"],
        "mag": w["magazine_size"], "reload_speed": w["reload_time"],
        "max_shoot_delay": w["fire_rate"], "reload_type": w["reload_type"],
        "recoil_pattern": w["recoil"], "formation": w["bullet_formation"],
    } for w in PRIMARY_WEAPONS
}

# ============================================================
# GAMEPLAY MODIFIERS
# ============================================================

MODIFIERS = [
    {"id": "gravity", "name": "Gravity Shift", "image": "assets/modifiers/gravity.png"},
    {"id": "speed", "name": "Speed Boost", "image": "assets/modifiers/speed.png"},
    {"id": "reload", "name": "Reload Mastery", "image": "assets/modifiers/reload.png"},
    {"id": "health", "name": "Max Health", "image": "assets/modifiers/health.png"},
]

selected_modifier = "gravity"
modifier_multiplier = 1.0
modifier_menu_open = False
modifier_multiplier_open = False
MODIFIER_MIN = 0.5
MODIFIER_MAX = 2.0


def get_modifier_multiplier(modifier_id):
    return modifier_multiplier if selected_modifier == modifier_id else 1.0


def calculate_effective_gravity():
    return GRAVITY * get_modifier_multiplier("gravity")


def calculate_effective_speed(speed):
    return speed * get_modifier_multiplier("speed")


def calculate_effective_reload_time(base_time):
    return base_time * get_modifier_multiplier("reload")


def calculate_effective_max_health(base_health):
    return round(base_health * get_modifier_multiplier("health"))


current_weapon = "pistol"
bullets = []
ammo_in_mag = {name: weapon["mag"] for name, weapon in WEAPONS.items()}
reload_end_time = {name: 0.0 for name in WEAPONS}
next_shot_time = {name: 0.0 for name in WEAPONS}
reload_state = {name: {"next_shell": 0.0, "active": False} for name in WEAPONS}
recoil_patterns = {}
recoil_pitch = 0.0
recoil_yaw = 0.0
recoil_state = {"pitch": 0.0, "yaw": 0.0}

player_max_hp = calculate_effective_max_health(
    calculate_max_hp(character_weight, character_height)
)
player_health = player_max_hp
remote_healths = {}

ak_shots = 0
ak_recoil_active = False

reticle = Entity(
    parent=camera.ui,
    model="circle",
    color=color.red,
    scale=0.009,
    position=(0, 0, -2),
)

reticle_dot = Entity(
    parent=camera.ui,
    model="quad",
    color=color.red,
    scale=(0.003, 0.003),
    position=(0, 0, -10),
)

health_text = Text(
    parent=camera.ui,
    text="Health: 100",
    position=(0.65, -0.46),
    scale=0.9,
    color=color.white,
)

remote_health_text = Text(
    parent=camera.ui,
    text="Opponent: 100",
    position=(0.65, -0.49),
    scale=0.8,
    color=color.red,
)

ammo_weapon_text = Text(
    parent=camera.ui,
    text="Pistol | Damage: 25",
    position=(0.65, -0.41),
    scale=0.8,
    color=color.white,
)

# Completely black screen shown while dead.
death_screen = Entity(
    parent=camera.ui,
    model="quad",
    color=color.black,
    scale=(2, 2),
    position=(0, 0, -20),
    enabled=False,
)

# ============================================================
# HEALTH UI
# ============================================================

def update_health_ui():
    health_text.text = f"Health: {player_health}/{player_max_hp}"

    remote_lines = []
    for pid, info in sorted(players.items()):
        if pid == player_number:
            continue

        state = info.get("state", {})
        max_hp = calculate_max_hp(
            state.get("weight", DEFAULT_WEIGHT),
            state.get("height", DEFAULT_HEIGHT),
        )
        hp = info.get("health", max_hp)
        name = info.get("name", f"Player {pid}")

        remote_lines.append(f"{name}: {hp}/{max_hp}")

    remote_health_text.text = "\n".join(remote_lines)

    weapon = WEAPONS[current_weapon]
    ammo = ammo_in_mag[current_weapon]
    mag = weapon["mag"]

    if reload_state[current_weapon]["active"]:
        status = " | RELOADING"
    else:
        status = ""

    ammo_weapon_text.text = (
        f"{current_weapon.title()} | "
        f"Ammo: {ammo}/{mag}{status}"
    )

def send_health_update():
    packet = {
        "type": "health",
        "player": player_number,
        "health": player_health,
    }

    if is_host:
        broadcast_packet(packet)
    else:
        send_packet(packet)

# ============================================================
# WEAPON FUNCTIONS
# ============================================================

def reload_weapon():
    weapon = WEAPONS[current_weapon]
    now = time.time()
    name = current_weapon

    if player_health <= 0 or menu_open or chat_open:
        return
    if ammo_in_mag[name] >= weapon["mag"] or reload_state[name]["active"]:
        return

    reload_state[name]["active"] = True
    effective_reload_time = calculate_effective_reload_time(weapon["reload_speed"])
    if weapon["reload_type"] == "single":
        reload_state[name]["next_shell"] = now + effective_reload_time
        reload_end_time[name] = now + effective_reload_time
    else:
        reload_end_time[name] = now + effective_reload_time

    update_health_ui()
    print(f"Reloading {name}...")


def select_weapon(name):
    global current_weapon, ak_shots, ak_recoil_active
    if name not in WEAPONS:
        return
    current_weapon = name
    ak_shots = 0
    ak_recoil_active = False
    gun.color = {"pistol": color.gray, "ak": color.dark_gray,
                 "shotgun": color.brown, "sniper": color.black}.get(name, color.gray)
    update_health_ui()


# ============================================================
# DEATH EXPLOSION
# ============================================================

explosion_particles = []


def create_explosion(position):
    for _ in range(32):
        particle = Entity(
            model="sphere",
            position=position,
            scale=0.07,
            color=random.choice([
                color.white, 
                color.smoke, 
                color.light_gray, 
                color.gray, 
                color.dark_gray, 
                color.black, 
                color.red, 
                color.orange, 
                color.yellow, 
                color.lime, 
                color.green, 
                color.turquoise, 
                color.cyan, 
                color.azure, 
                color.blue, 
                color.violet, 
                color.magenta, 
                color.pink, 
                color.brown, 
                color.olive, 
                color.peach, 
                color.gold, 
                color.salmon
            ]),
        )

        direction = Vec3(
            random.uniform(-1, 1),
            random.uniform(-0.2, 1.2),
            random.uniform(-1, 1),
        ).normalized()

        explosion_particles.append({
            "entity": particle,
            "velocity": direction * random.uniform(3.5, 8),
            "life": 0.65,
        })


def update_explosions(dt):
    for p in explosion_particles[:]:
        particle = p["entity"]
        p["life"] -= dt

        if p["life"] <= 0:
            destroy(particle)
            explosion_particles.remove(p)
            continue

        p["velocity"].y -= 9 * dt
        particle.position += p["velocity"] * dt
        particle.scale *= max(0, 1 - dt * 1.8)


# ============================================================
# DAMAGE AND RESPAWN
# ============================================================

def damage_local(amount):
    global player_health, local_respawn_at

    if player_health <= 0:
        return

    player_health = max(0, player_health - amount)

    send_health_update()
    update_health_ui()

    if player_health == 0:
        print("You were eliminated!")

        create_explosion(
            local_body.position + Vec3(0, 0.8, 0)
        )

        local_body.enabled = False
        gun.enabled = False

        # Hide the normal HUD and show the black screen.
        reticle.enabled = False
        reticle_dot.enabled = False
        health_text.enabled = False
        remote_health_text.enabled = False
        ammo_weapon_text.enabled = False

        death_screen.enabled = True

        mouse.locked = False
        mouse.visible = False

        local_respawn_at = time.time() + 2.0


def damage_remote(amount):
    # The opponent's computer controls their actual health.
    # We only send the shot; their computer calculates damage.
    pass

def leave_game():
    global has_left, session_started, network_ready
    global player_number, host_address, is_host
    global local_respawn_at, remote_respawn_at

    if has_left:
        return

    has_left = True

    # Cancel any pending respawn.
    local_respawn_at = 0.0
    remote_respawn_at = 0.0

    # Create the departure explosion.
    create_explosion(local_body.position + Vec3(0, 0.8, 0))

    # Remove the local player from gameplay.
    local_body.enabled = False
    gun.enabled = False

    # Tell the network that this player has left.
    if network_ready:
        if is_host:
            broadcast_packet({"type": "match_ended"})
        else:
            send_packet({
                "type": "leave",
                "player": player_number,
            })

    # Stop this player's match.
    session_started = False
    network_ready = False
    discovery_active = False

    for pid in list(player_entities):
        remove_player_entity(pid)

    players.clear()

    # Hide gameplay UI.
    for obj in [
        reticle, reticle_dot, health_text,
        remote_health_text, ammo_weapon_text,
        player_list_bg, player_list_title,
        player_list_headers, player_list_text,
        death_screen,
    ]:
        obj.enabled = False

    # Return to the home screen.
    mouse.locked = False
    mouse.visible = True
    show_home_screen()

def global_local_respawn():
    global player_health, local_respawn_at
    global start_x, start_z

    if has_left:
        return

    start_x, start_z = find_valid_spawn(
        character_height,
        character_weight,
    )

    player_health = player_max_hp
    local_respawn_at = 0.0

    local_state["x"] = start_x
    local_state["z"] = start_z

    local_body.position = (
        start_x,
        character_height / 2,
        start_z,
    )

    camera.position = (
        start_x,
        STAND_EYE_HEIGHT,
        start_z,
    )

    local_body.enabled = True
    gun.enabled = True

    death_screen.enabled = False

    reticle.enabled = True
    reticle_dot.enabled = True
    health_text.enabled = True
    remote_health_text.enabled = True
    ammo_weapon_text.enabled = True

    update_health_ui()
    send_health_update()

    respawn_packet = {
        "type": "respawn",
        "player": player_number,
        "x": start_x,
        "z": start_z,
    }

    if is_host:
        broadcast_packet(respawn_packet)
    else:
        send_packet(respawn_packet)

    mouse.locked = True
    mouse.visible = False

def global_remote_respawn():
    global remote_health, remote_respawn_at

    remote_health = MAX_HEALTH
    remote_respawn_at = 0.0

    remote_state["x"] = 10 if is_host else -10
    remote_state["z"] = 0.0

    # Remote player visuals are managed by player_entities (four-player system).
    remote_body.enabled = False
    remote_head.enabled = False

    update_health_ui()

    send_packet({
        "type": "respawn",
        "x": remote_state["x"],
        "z": 0.0,
    })


# ============================================================
# BULLETS AND SHOOTING
# ============================================================

def spawn_bullet(direction, damage, speed):
    bullet = Entity(
        model="sphere",
        color=color.green,
        scale=0.07,
        position=gun.world_position + camera.forward * 0.5,
    )

    bullet.direction = direction.normalized()
    bullet.damage = int(damage)
    bullet.speed = speed
    bullet.alive = True

    bullets.append(bullet)

def process_remote_shot(message):
    shooter_id = int(message.get("shooter", 0))
    # Never process our own shots as incoming damage.
    if shooter_id == player_number:
        return
    incoming_id = int(message.get("shot_id", 0))

    # Track shot IDs separately for each shooter
    previous_id = remote_last_shot_ids.get(shooter_id, 0)

    if incoming_id <= previous_id:
        return

    remote_last_shot_ids[shooter_id] = incoming_id

    # Get the shot information
    origin = Vec3(
        message["origin"][0],
        message["origin"][1],
        message["origin"][2]
    )

    direction = Vec3(
        message["direction"][0],
        message["direction"][1],
        message["direction"][2]
    ).normalized()

    weapon = WEAPONS.get(message.get("weapon", "pistol"), WEAPONS["pistol"])

    # Ignore the shooter's own hitbox so the shot doesn't hit
    # the shooter before reaching its target.
    ignored = [remote_body, remote_head, gun]

    shooter_entity = player_entities.get(shooter_id)
    if shooter_entity:
        ignored.append(shooter_entity["hitbox"])

    # Check whether the incoming shot intersects our hitbox
    hit = raycast(
        origin,
        direction,
        distance=200,
        ignore=ignored
    )

    if hit.hit and hit.entity == local_body:
        print(f"YOU WERE HIT BY PLAYER {shooter_id}")
        damage_local(weapon["damage"])

def parse_recoil_pattern(pattern):
    """Parse amount+direction+duration groups, e.g. 5u0.1s2r0.2s."""
    parts = re.findall(r"(\d+(?:\.\d+)?)([lrud])(\d+(?:\.\d+)?)s", pattern.lower())
    return [(float(amount), direction, float(duration)) for amount, direction, duration in parts]


def advance_recoil(dt):
    """Advance the held weapon's repeating recoil sequence."""
    global pitch, yaw
    name = current_weapon
    state = recoil_patterns.setdefault(name, {"index": 0, "elapsed": 0.0, "last_release": 0.0, "gun_x": 0.0, "gun_y": 0.0})
    held = action_held("fire") and not menu_open and not chat_open and player_health > 0

    if not held:
        if state.get("was_held", False):
            state["last_release"] = time.time()
        state["was_held"] = False
        return

    if not state.get("was_held", False):
        if time.time() - state["last_release"] >= 1.0:
            state["index"] = 0
            state["elapsed"] = 0.0
        state["was_held"] = True

    pattern = parse_recoil_pattern(WEAPONS[name]["recoil_pattern"])
    if not pattern:
        return

    # Process partial frame time accurately, including pattern boundaries.
    remaining = dt
    while remaining > 0 and pattern:
        index = state["index"] % len(pattern)
        amount, direction, duration = pattern[index]
        duration = max(duration, 0.0001)
        available = duration - state["elapsed"]
        step = min(remaining, available)
        movement = amount * (step / duration)

        if direction == "u":
            pitch += movement
            state["gun_y"] += movement * 0.002
        elif direction == "d":
            pitch -= movement
            state["gun_y"] -= movement * 0.002
        elif direction == "r":
            yaw += movement
            state["gun_x"] += movement * 0.002
        elif direction == "l":
            yaw -= movement
            state["gun_x"] -= movement * 0.002

        state["elapsed"] += step
        remaining -= step
        if state["elapsed"] >= duration - 1e-8:
            state["elapsed"] = 0.0
            state["index"] = (state["index"] + 1) % len(pattern)


def shoot():
    global shot_id
    if not network_ready or not session_started or menu_open or chat_open:
        return

    now = time.time()
    weapon = WEAPONS[current_weapon]
    if reload_state[current_weapon]["active"] or ammo_in_mag[current_weapon] <= 0:
        return
    if now < next_shot_time[current_weapon]:
        return

    shot_id += 1
    next_shot_time[current_weapon] = now + weapon["max_shoot_delay"]
    ammo_in_mag[current_weapon] -= 1

    origin = camera.world_position
    base_direction = camera.forward
    count = max(1, int(weapon["bullets"]))
    for _ in range(count):
        direction = base_direction
        if weapon["formation"] == "spread" and weapon["spread"]:
            direction = (base_direction + Vec3(
                random.uniform(-weapon["spread"], weapon["spread"]) / 100,
                random.uniform(-weapon["spread"], weapon["spread"]) / 100,
                random.uniform(-weapon["spread"], weapon["spread"]) / 100,
            )).normalized()
        spawn_bullet(direction, weapon["damage"], weapon["speed"])

    shot_message = {
        "type": "shot", "shot_id": shot_id, "shooter": player_number,
        "weapon": current_weapon,
        "origin": [origin.x, origin.y, origin.z],
        "direction": [base_direction.x, base_direction.y, base_direction.z],
        "damage": weapon["damage"],
    }
    process_remote_shot(shot_message)
    if is_host:
        broadcast_packet(shot_message)
    else:
        send_packet(shot_message)
    update_health_ui()
    if ammo_in_mag[current_weapon] == 0:
        reload_weapon()


def update_bullets(dt):
    for bullet in bullets[:]:
        if not bullet.alive:
            continue

        distance = bullet.speed * dt
        direction = bullet.direction

        hit = raycast(
            bullet.position,
            direction,
            distance=distance,
            ignore=[bullet, gun, local_body],
        )

        if hit.hit:
            target = hit.entity

            if getattr(target, "is_remote_player", False):
                pass

            destroy(bullet)
            bullets.remove(bullet)
            continue

        bullet.position += direction * distance

        if (
            abs(bullet.x) > ARENA_HALF + 100
            or abs(bullet.z) > ARENA_HALF + 100
            or abs(bullet.y) > WALL_HEIGHT + 100
        ):
            destroy(bullet)
            bullets.remove(bullet)


# ============================================================
# SETTINGS STATE
# ============================================================

settings = {
    "fov": 90,
    "sens_x": 100,
    "sens_y": 100,
    "ads_sens_x": 45,
    "ads_sens_y": 45,
    "sprint_mode": "Toggle",
    "crouch_mode": "Hold",
    "fps_display": True,
    "reticle_outline": True,
    "reticle_inside": True,
    "reticle_outline_r": 255,
    "reticle_outline_g": 0,
    "reticle_outline_b": 0,
    "reticle_inside_r": 255,
    "reticle_inside_g": 0,
    "reticle_inside_b": 0,
    "reticle_border_size": 5,
}

window.fps_counter.enabled = settings["fps_display"]

# === BINDING LOGIC START ===
# ============================================================
# KEY BINDINGS
# ============================================================
# Every action has two slots. One action can own two keys, but a key can
# only ever belong to one action.

BIND_ACTIONS = [
    ("move_forward", "Move forward"),
    ("move_back", "Move back"),
    ("move_left", "Move left"),
    ("move_right", "Move right"),
    ("jump", "Jump"),
    ("sprint", "Sprint"),
    ("crouch", "Crouch"),
    ("fire", "Fire"),
    ("aim", "Aim"),
    ("reload", "Reload"),
    ("player_list", "Player list"),
    ("chat", "Chat"),
]
BIND_LABELS = dict(BIND_ACTIONS)

DEFAULT_BINDS = {
    "move_forward": ["w", ""],
    "move_back": ["s", ""],
    "move_left": ["a", ""],
    "move_right": ["d", ""],
    "jump": ["space", ""],
    "sprint": ["shift", ""],
    "crouch": ["control", ""],
    "fire": ["left mouse", ""],
    "aim": ["right mouse", ""],
    "reload": ["r", ""],
    "player_list": ["tab", ""],
    "chat": ["/", ""],
}


def fresh_binds():
    return {action: list(keys) for action, keys in DEFAULT_BINDS.items()}


settings["binds"] = fresh_binds()

BIND_KEY_ALIASES = {
    "left shift": "shift", "right shift": "shift",
    "left control": "control", "right control": "control",
    "left alt": "alt", "right alt": "alt",
}
BIND_RESERVED_KEYS = ("escape", "enter")   # Esc = menu / cancel, Enter = send chat
PRESS_NAME_EXCEPTIONS = ("scroll up", "scroll down", "page up", "page down")
IGNORED_EVENT_SUFFIXES = (" hold", " drag", " double click")
SCROLL_PULSE_SECONDS = 0.12

_last_press_time = {}
key_pulse = {}

KEY_DISPLAY = {
    "left mouse": "Mouse Left",
    "right mouse": "Mouse Right",
    "middle mouse": "Mouse Mid",
    "scroll up": "Scroll Up",
    "scroll down": "Scroll Down",
    "control": "Ctrl",
    "shift": "Shift",
    "alt": "Alt",
    "space": "Space",
    "tab": "Tab",
    "enter": "Enter",
    "escape": "Esc",
}


def display_key(name):
    if name in KEY_DISPLAY:
        return KEY_DISPLAY[name]
    return name.upper() if len(name) == 1 else name.title()


def press_event_name(key):
    """Turn a raw input event into a bindable key name.
    Returns None for releases, holds and other non-press events."""
    if key in PRESS_NAME_EXCEPTIONS:
        name = key
    else:
        if key.endswith(" up") or key.endswith(IGNORED_EVENT_SUFFIXES) or key == "mouse move":
            return None
        name = key[:-5] if key.endswith(" mouse down") else key

    name = BIND_KEY_ALIASES.get(name, name)

    # Some keys can arrive twice in the same instant (e.g. shift and
    # left shift); ignore the duplicate.
    if not name.startswith("scroll"):
        now = time.time()
        if now - _last_press_time.get(name, -1.0) < 0.02:
            return None
        _last_press_time[name] = now

    return name


def is_key_down(name):
    if name.startswith("scroll"):
        # The wheel has no "held" state, so it counts as held briefly.
        return time.time() < key_pulse.get(name, 0.0)
    return bool(held_keys[name])


def action_held(action):
    for name in settings["binds"][action]:
        if name and is_key_down(name):
            return True
    return False


def action_for_key(name):
    for action, keys in settings["binds"].items():
        if name in keys:
            return action
    return None


def try_bind(action, slot, name):
    """Bind `name` to one slot of `action`. Returns (ok, message)."""
    keys = settings["binds"][action]

    if keys[slot] == name:
        return True, ""

    if name in BIND_RESERVED_KEYS:
        return False, f"{display_key(name)} is reserved"

    owner = action_for_key(name)

    if owner == action:
        return False, f"{display_key(name)} is already set on {BIND_LABELS[action]}"

    if owner is not None:
        return False, (
            f"{display_key(name)} is already used by {BIND_LABELS[owner]}"
            " - clear it first"
        )

    keys[slot] = name
    return True, ""
# === BINDING LOGIC END ===

player_name = "Player"
local_respawn_at = 0.0
remote_respawn_at = 0.0
shot_id = 0
remote_last_shot_ids = {}
menu_open = True
settings_open = False
chat_open = False
has_left = False
is_aiming = False
is_crouching = False
sprint_toggled = False
crouch_toggled = False
pitch = 0.0
vertical_velocity = 0.0
is_grounded = True
GRAVITY = 386.09
yaw = local_state["yaw"]


# ============================================================
# UI HELPERS
# ============================================================

def make_button(parent, text, position, scale):
    return Button(
        parent=parent,
        text=text,
        position=position,
        scale=scale,
        color=BG_BUTTON,
        highlight_color=BG_HOVER,
        pressed_color=BG_PRESSED,
        text_color=TEXT_MAIN,
    )


def make_rounded_rectangle(width=1, height=1, radius=0.06, segments=10):
    vertices = []

    corners = [
        (width / 2 - radius, height / 2 - radius, 0, 90),
        (-width / 2 + radius, height / 2 - radius, 90, 180),
        (-width / 2 + radius, -height / 2 + radius, 180, 270),
        (width / 2 - radius, -height / 2 + radius, 270, 360),
    ]

    for cx, cy, start_angle, end_angle in corners:
        for i in range(segments + 1):
            angle = math.radians(
                start_angle
                + (end_angle - start_angle) * i / segments
            )

            vertices.append((
                cx + math.cos(angle) * radius,
                cy + math.sin(angle) * radius,
                0,
            ))

    center_index = len(vertices)
    vertices.append((0, 0, 0))

    triangles = []

    for i in range(center_index):
        triangles.append((
            center_index,
            i,
            (i + 1) % center_index,
        ))

    return Mesh(
        vertices=vertices,
        triangles=triangles,
        mode="triangle",
        static=True,
    )


# ============================================================
# HUD
# ============================================================

player_list_bg = Entity(
    parent=camera.ui,
    model="quad",
    color=TAB,
    scale=(0.55, 0.12),
    position=(0, 0, 0),
    enabled=False,
)

player_list_title = Text(
    parent=camera.ui,
    text="PLAYERS",
    origin=(0, 0),
    position=(0, 0.035, -1),
    scale=1,
    color=color.white,
    enabled=False,
)

player_list_headers = Text(
    parent=camera.ui,
    text="PLAYER                         STATUS",
    origin=(0, 0),
    position=(0, -0.005, -1),
    scale=0.7,
    color=color.gray,
    enabled=False,
)

player_list_text = Text(
    parent=camera.ui,
    text="",
    origin=(0, 0),
    position=(0, -0.035, -1),
    scale=0.8,
    color=color.white,
    enabled=False,
)

Text(
    parent=camera.ui,
    text="WASD Move | Shift Sprint | Ctrl Crouch | RMB Aim | / Chat | Esc Menu",
    position=(-0.85, -0.46),
    scale=0.7,
    color=TEXT_MAIN,
)

# ============================================================
# MAIN MENU
# ============================================================

menu_bg = Entity(
    parent=camera.ui,
    model="quad",
    color=BG_PANEL,
    scale=(0.48, 0.48),
    position=(0, 0, 0.5),
    shader=unlit_shader,
    enabled=False,
)

menu_title = Text(
    parent=camera.ui,
    text="PAUSED",
    y=0.16,
    scale=1.8,
    origin=(0, 0),
    color=TEXT_MAIN,
    z=-0.1,
    enabled=False,
)

settings_button = make_button(
    camera.ui,
    "SETTINGS",
    (0, 0.035),
    (0.30, 0.065),
)
settings_button.enabled = False

leave_button = make_button(
    camera.ui,
    "LEAVE GAME",
    (0, -0.15),
    (0.30, 0.065),
)

leave_button.enabled = False
leave_button.color = color.violet
leave_button.highlight_color = color.azure

name_label = Text(
    parent=camera.ui,
    text="PLAYER NAME",
    x=-0.145,
    y=-0.045,
    scale=0.8,
    color=TEXT_MUTED,
    z=-0.1,
    enabled=False,
)

name_input = InputField(
    parent=camera.ui,
    default_value=player_name,
    y=-0.12,
    scale=(0.30, 0.05),
    enabled=False,
)
name_input.text_field.alignment = TextNode.ACenter

# ============================================================
# SETTINGS PANEL
# ============================================================

settings_bg = Entity(
    parent=camera.ui,
    model="quad",
    color=BG_PANEL,
    scale=(2, 2),
    position=(0, 0, 10),
    shader=unlit_shader,
    enabled=False,
)

settings_title = Text(
    parent=camera.ui,
    text="SETTINGS",
    y=0.39,
    scale=1.8,
    origin=(0, 0),
    color=TEXT_MAIN,
    z=-0.1,
    enabled=False,
)

settings_subtitle = Text(
    parent=camera.ui,
    text="Customize your gameplay",
    y=0.345,
    scale=0.8,
    origin=(0, 0),
    color=TEXT_MUTED,
    z=-0.1,
    enabled=False,
)

# ------------------------------------------------------------
# SETTINGS TABS
# ------------------------------------------------------------

settings_tab = "Video"
settings_tab_buttons = {}

def switch_settings_tab(tab):
    global settings_tab, game_scroll
    settings_tab = tab
    game_scroll = 0.0
    refresh_settings_tabs()


def create_settings_tab(name, x):
    button = make_button(
        camera.ui,
        name,
        (x, 0.27),
        (0.19, 0.055),
    )

    button.enabled = False
    button.on_click = lambda: switch_settings_tab(name)

    settings_tab_buttons[name] = button


create_settings_tab("Video", -0.20)
create_settings_tab("Audio", 0.0)
create_settings_tab("Game", 0.20)


# ------------------------------------------------------------
# SETTINGS HEADERS
# ------------------------------------------------------------

sensitivity_header = Text(
    parent=camera.ui,
    text="SENSITIVITY",
    position=(0, 0.19),
    origin=(0, 0),
    scale=1.1,
    color=TEXT_MAIN,
    enabled=False,
)

reticle_header = Text(
    parent=camera.ui,
    text="RETICLE",
    position=(0, -0.32),
    origin=(0, 0),
    scale=1.1,
    color=TEXT_MAIN,
    enabled=False,
)


# ------------------------------------------------------------
# SLIDERS
# ------------------------------------------------------------

slider_objects = []
slider_labels = []


def make_slider(label, key, y, minimum, maximum, default):
    label_text = Text(
        parent=camera.ui,
        text=label,
        x=-0.39,
        y=y + 0.025,
        scale=0.8,
        color=TEXT_MAIN,
        enabled=False,
    )

    slider_labels.append(label_text)

    slider = Slider(
        min=minimum,
        max=maximum,
        default=default,
        step=1,
        dynamic=True,
        x=-0.05,
        y=y,
        scale=0.55,
        enabled=False,
    )

    value_text = Text(
        parent=camera.ui,
        text=str(default),
        x=0.35,
        y=y + 0.02,
        scale=0.8,
        color=TEXT_MAIN,
        enabled=False,
    )

    slider_objects.append((slider, value_text, key))

    return slider


# Game tab: Sensitivity section.

fov_slider = make_slider(
    "Field of view", "fov", 0.12, 60, 120, 90
)

sens_x_slider = make_slider(
    "Horizontal sensitivity", "sens_x", 0.02, 10, 300, 100
)

sens_y_slider = make_slider(
    "Vertical sensitivity", "sens_y", -0.04, 10, 300, 100
)

ads_x_slider = make_slider(
    "ADS horizontal", "ads_sens_x", -0.14, 5, 200, 45
)

ads_y_slider = make_slider(
    "ADS vertical", "ads_sens_y", -0.20, 5, 200, 45
)


# Reticle controls. These are placed below Sensitivity; use the mouse wheel
# while the Game tab is open to scroll the whole Game settings list.
reticle_outline_toggle = make_button(
    camera.ui, "Outline: ON", (-0.16, -0.39), (0.29, 0.045)
)
reticle_inside_toggle = make_button(
    camera.ui, "Inside Reticle: ON", (0.16, -0.39), (0.29, 0.045)
)
reticle_outline_toggle.enabled = False
reticle_inside_toggle.enabled = False

# Same spacing logic as the sensitivity sliders: related sliders sit close
# together, and each new group gets the larger gap.
reticle_slider_ys = [
    -0.52,  # Outline red
    -0.58,  # Outline green
    -0.64,  # Outline blue
    -0.74,  # Inside red
    -0.80,  # Inside green
    -0.86,  # Inside blue
    -0.96,  # Border size
]
reticle_slider_keys = [
    ("Outline red", "reticle_outline_r"),
    ("Outline green", "reticle_outline_g"),
    ("Outline blue", "reticle_outline_b"),
    ("Inside red", "reticle_inside_r"),
    ("Inside green", "reticle_inside_g"),
    ("Inside blue", "reticle_inside_b"),
    ("Border size", "reticle_border_size"),
]
reticle_slider_objects = []
for index, (label, key) in enumerate(reticle_slider_keys):
    y = reticle_slider_ys[index]
    slider = make_slider(label, key, y, 0, 255 if key != "reticle_border_size" else 10, settings[key])
    reticle_slider_objects.append((slider, next(v for v in slider_objects if v[0] is slider)[1], key))




# ------------------------------------------------------------
# VIDEO TAB: FPS DISPLAY
# ------------------------------------------------------------

fps_toggle = make_button(
    camera.ui,
    "FPS Display: ON",
    (0, 0.12),
    (0.35, 0.06),
)

fps_toggle.enabled = False


def toggle_fps_display():
    settings["fps_display"] = not settings["fps_display"]

    window.fps_counter.enabled = settings["fps_display"]

    fps_toggle.text = (
        "FPS Display: ON"
        if settings["fps_display"]
        else "FPS Display: OFF"
    )


fps_toggle.on_click = toggle_fps_display


# ------------------------------------------------------------
# SPRINT / CROUCH MODE TOGGLES (shown in the Game tab, under Controls)
# ------------------------------------------------------------

sprint_toggle = make_button(
    camera.ui,
    "Sprint Mode: Toggle",
    (-0.16, -1.89),
    (0.29, 0.05),
)

crouch_toggle = make_button(
    camera.ui,
    "Crouch Mode: Hold",
    (0.16, -1.89),
    (0.29, 0.05),
)

sprint_toggle.enabled = False
crouch_toggle.enabled = False


settings_back_button = make_button(
    camera.ui,
    "BACK",
    (0, -0.36),
    (0.3, 0.06),
)

settings_back_button.enabled = False


def toggle_sprint():
    global sprint_toggled

    settings["sprint_mode"] = (
        "Toggle"
        if settings["sprint_mode"] == "Hold"
        else "Hold"
    )

    sprint_toggled = False
    sprint_toggle.text = f"Sprint: {settings['sprint_mode']}"


def toggle_crouch():
    global crouch_toggled

    settings["crouch_mode"] = (
        "Toggle"
        if settings["crouch_mode"] == "Hold"
        else "Hold"
    )

    crouch_toggled = False
    crouch_toggle.text = f"Crouch: {settings['crouch_mode']}"


sprint_toggle.on_click = toggle_sprint
crouch_toggle.on_click = toggle_crouch


# ENABLE / DISABLE MOVEMENT OPTIONS

def toggle_sprint():
    global sprint_toggled

    settings["sprint_mode"] = (
        "Toggle"
        if settings["sprint_mode"] == "Hold"
        else "Hold"
    )

    sprint_toggled = False
    refresh_settings_tabs()


def toggle_crouch():
    global crouch_toggled

    settings["crouch_mode"] = (
        "Toggle"
        if settings["crouch_mode"] == "Hold"
        else "Hold"
    )

    crouch_toggled = False
    refresh_settings_tabs()


sprint_toggle.on_click = toggle_sprint
crouch_toggle.on_click = toggle_crouch


# ------------------------------------------------------------
# GAME TAB: CONTROLS (KEY BINDS)
# ------------------------------------------------------------

SETTINGS_SUBTITLE_DEFAULT = "Customize your gameplay"
LISTEN_PROMPT = "Press a key or mouse button  (Esc cancels, Backspace clears)"

CONTROLS_HEADER_Y = -1.08
BIND_ROW_START_Y = -1.20
BIND_ROW_SPACING = 0.055
RESET_BINDS_Y = -1.97

controls_header = Text(
    parent=camera.ui,
    text="CONTROLS",
    position=(0, CONTROLS_HEADER_Y),
    origin=(0, 0),
    scale=1.1,
    color=TEXT_MAIN,
    enabled=False,
)

bind_buttons = {}
bind_row_labels = {}
bind_listen = {"target": None, "since": 0.0}
settings_notice_token = [0]

for _index, (_action, _label) in enumerate(BIND_ACTIONS):
    _y = BIND_ROW_START_Y - _index * BIND_ROW_SPACING
    bind_row_labels[_action] = Text(
        parent=camera.ui,
        text=_label,
        x=-0.39,
        y=_y,
        origin=(-0.5, 0),
        scale=0.8,
        color=TEXT_MAIN,
        enabled=False,
    )
    for _slot, _x in enumerate((0.02, 0.22)):
        _button = make_button(camera.ui, "-", (_x, _y), (0.18, 0.042))
        _button.enabled = False
        _button.on_click = (lambda a=_action, sl=_slot: start_listening(a, sl))
        bind_buttons[(_action, _slot)] = _button

reset_binds_button = make_button(
    camera.ui, "Reset controls", (0, RESET_BINDS_Y), (0.30, 0.05)
)
reset_binds_button.enabled = False


def set_settings_status(text, status_color=None, seconds=None):
    settings_subtitle.text = text
    settings_subtitle.color = status_color if status_color is not None else TEXT_MUTED
    settings_notice_token[0] += 1

    if seconds is not None:
        token = settings_notice_token[0]
        invoke(restore_settings_status, token, delay=seconds)


def restore_settings_status(token=None):
    if token is not None and token != settings_notice_token[0]:
        return

    if bind_listen["target"] is not None:
        set_settings_status(LISTEN_PROMPT, color.orange)
    else:
        set_settings_status(SETTINGS_SUBTITLE_DEFAULT)


def refresh_bind_buttons():
    for (action, slot), button in bind_buttons.items():
        listening = bind_listen["target"] == (action, slot)
        name = settings["binds"][action][slot]
        button.text = "Press key" if listening else (display_key(name) if name else "-")
        button.color = TAB if listening else BG_BUTTON


def start_listening(action, slot):
    bind_listen["target"] = (action, slot)
    bind_listen["since"] = time.time()
    set_settings_status(LISTEN_PROMPT, color.orange)
    refresh_bind_buttons()


def stop_listening():
    bind_listen["target"] = None
    set_settings_status(SETTINGS_SUBTITLE_DEFAULT)
    refresh_bind_buttons()


def handle_bind_capture(name):
    """Called from input() while a slot is waiting for a key."""
    if name is None:
        return

    action, slot = bind_listen["target"]

    if name == "escape":
        stop_listening()
        return

    if name in ("backspace", "delete"):
        settings["binds"][action][slot] = ""
        stop_listening()
        return

    if name == "left mouse":
        # Ignore the click that started listening, and clicks on bind
        # buttons (those just pick a different slot).
        if time.time() - bind_listen["since"] < 0.25:
            return
        if mouse.hovered_entity in bind_buttons.values() or mouse.hovered_entity is reset_binds_button:
            return

    ok, message = try_bind(action, slot, name)

    if ok:
        stop_listening()
    else:
        set_settings_status(message, color.red, seconds=2.5)


def reset_binds():
    settings["binds"] = fresh_binds()
    stop_listening()


reset_binds_button.on_click = reset_binds


# ------------------------------------------------------------
# GAME TAB SCROLLING
# ------------------------------------------------------------
# Everything in the Game tab (headers, labels, sliders, value text, toggles,
# key binds) moves together. The BACK button never moves; anything that
# scrolls into the band around it (or up under the tab buttons) is hidden.

GAME_CLIP_BOTTOM = -0.30   # centers below this are hidden (BACK button zone)
GAME_CLIP_TOP_ROW = 0.20   # headers / toggles / bind rows
GAME_CLIP_TOP_SLIDER = 0.17  # sliders (their label sits above them)
GAME_SCROLL_STEP = 0.15

game_scroll = 0.0


def _reticle_row_visible(key):
    if key.startswith("reticle_outline_") or key == "reticle_border_size":
        return settings["reticle_outline"]
    if key.startswith("reticle_inside_"):
        return settings["reticle_inside"]
    return True


# Each row: (list of (entity, base_y), clip_top, condition function)
game_scroll_rows = [
    ([(sensitivity_header, sensitivity_header.y)], GAME_CLIP_TOP_ROW, lambda: True),
]
for (_slider, _value_text, _key), _label in zip(slider_objects, slider_labels):
    game_scroll_rows.append((
        [(_slider, _slider.y), (_value_text, _value_text.y), (_label, _label.y)],
        GAME_CLIP_TOP_SLIDER,
        (lambda k=_key: _reticle_row_visible(k)),
    ))
game_scroll_rows.append(
    ([(reticle_header, reticle_header.y)], GAME_CLIP_TOP_ROW, lambda: True)
)
game_scroll_rows.append((
    [
        (reticle_outline_toggle, reticle_outline_toggle.y),
        (reticle_inside_toggle, reticle_inside_toggle.y),
    ],
    GAME_CLIP_TOP_ROW,
    lambda: True,
))
game_scroll_rows.append(
    ([(controls_header, controls_header.y)], GAME_CLIP_TOP_ROW, lambda: True)
)
for _action, _label in BIND_ACTIONS:
    game_scroll_rows.append((
        [
            (bind_row_labels[_action], bind_row_labels[_action].y),
            (bind_buttons[(_action, 0)], bind_buttons[(_action, 0)].y),
            (bind_buttons[(_action, 1)], bind_buttons[(_action, 1)].y),
        ],
        GAME_CLIP_TOP_ROW,
        lambda: True,
    ))
game_scroll_rows.append((
    [(sprint_toggle, sprint_toggle.y), (crouch_toggle, crouch_toggle.y)],
    GAME_CLIP_TOP_ROW,
    lambda: True,
))
game_scroll_rows.append(
    ([(reset_binds_button, reset_binds_button.y)], GAME_CLIP_TOP_ROW, lambda: True)
)

_lowest_base_y = min(row[0][0][1] for row in game_scroll_rows)
GAME_SCROLL_MAX = max(0.0, -0.28 - _lowest_base_y)


def apply_game_scroll(tab_visible):
    """Reposition every Game-tab widget for the current scroll offset and
    show only the ones that are inside the visible window."""
    if not tab_visible and bind_listen["target"] is not None:
        stop_listening()

    for entities, clip_top, condition in game_scroll_rows:
        ref_y = entities[0][1] + game_scroll
        visible = (
            tab_visible
            and condition()
            and GAME_CLIP_BOTTOM <= ref_y <= clip_top
        )
        for entity, base_y in entities:
            entity.y = base_y + game_scroll
            entity.enabled = visible


def hide_settings_widgets():
    """Hide every settings widget: tab buttons, Video tab and Game tab."""
    for button in settings_tab_buttons.values():
        button.enabled = False

    fps_toggle.enabled = False
    apply_game_scroll(False)


def toggle_reticle_outline():
    settings["reticle_outline"] = not settings["reticle_outline"]
    refresh_settings_tabs()

def toggle_reticle_inside():
    settings["reticle_inside"] = not settings["reticle_inside"]
    refresh_settings_tabs()

reticle_outline_toggle.on_click = toggle_reticle_outline
reticle_inside_toggle.on_click = toggle_reticle_inside


def refresh_settings():
    camera.fov = settings["fov"]

    for slider, value_text, key in slider_objects:
        slider.value = settings[key]
        value_text.text = str(int(slider.value))

    refresh_settings_tabs()


def refresh_settings_tabs():

    # Highlight the selected tab.
    for name, button in settings_tab_buttons.items():
        button.text = (
            f"[ {name} ]"
            if name == settings_tab
            else name
        )

    # VIDEO TAB.
    fps_toggle.enabled = settings_tab == "Video"

    fps_toggle.text = (
        "FPS Display: ON"
        if settings["fps_display"]
        else "FPS Display: OFF"
    )

    # GAME TAB.
    game_enabled = settings_tab == "Game"

    # Positions + visibility of every Game-tab widget (scrolled / clipped).
    apply_game_scroll(game_enabled)

    reticle_outline_toggle.text = (
        "Outline: ON" if settings["reticle_outline"] else "Outline: OFF"
    )
    reticle_inside_toggle.text = (
        "Inside Reticle: ON" if settings["reticle_inside"] else "Inside Reticle: OFF"
    )

    # Sprint / crouch mode toggles are positioned by the Game-tab scroll list.
    refresh_bind_buttons()

    sprint_toggle.text = f"Sprint Mode: {settings['sprint_mode']}"
    crouch_toggle.text = f"Crouch Mode: {settings['crouch_mode']}"

def show_menu():
    global menu_open, settings_open, menu_screen, settings_return_screen

    gun.enabled = False
    menu_screen = "pause"
    settings_return_screen = "pause"
    hide_all_frontend()
    menu_open = True
    settings_open = False

    for obj in [
        menu_bg,
        menu_title,
        settings_button,
        leave_button, 
        name_label,
        name_input,
    ]:
        obj.enabled = True

    for obj in [
        settings_bg,
        settings_title,
        settings_subtitle,
        sprint_toggle,
        crouch_toggle,
        settings_back_button,
    ]:
        obj.enabled = False

    for button in settings_tab_buttons.values():
        button.enabled = False

    for label in slider_labels:
        label.enabled = False

    for slider, value_text, key in slider_objects:
        slider.enabled = False
        value_text.enabled = False
    hide_settings_widgets()

    for obj in [home_background, home_title, home_subtitle, home_join_button, home_host_button, home_settings_button, home_quit_button, name_label, name_input, height_label, height_value, height_slider, weight_label, weight_value, weight_slider, width_value]:
        obj.enabled = False
    mouse.locked = False
    mouse.visible = True


def hide_menu():
    global menu_open, settings_open

    menu_open = False
    settings_open = False

    for obj in [
        menu_bg,
        menu_title,
        settings_button,
        leave_button,
        name_label,
        name_input,
        settings_bg,
        settings_title,
        settings_subtitle,
        sprint_toggle,
        crouch_toggle,
        settings_back_button,
        height_label,
        height_value,
        height_slider,
        weight_label,
        weight_value,
        weight_slider,
        width_value,
    ]:
        obj.enabled = False

    for button in settings_tab_buttons.values():
        button.enabled = False

    for label in slider_labels:
        label.enabled = False

    for slider, value_text, key in slider_objects:
        slider.enabled = False
        value_text.enabled = False
    hide_settings_widgets()

    window.position = window.position

    mouse.locked = True
    mouse.visible = False
    for obj in [reticle, reticle_dot, health_text, remote_health_text, ammo_weapon_text, gun]:
        obj.enabled = True


def show_settings():
    global settings_open, game_scroll

    settings_open = True
    game_scroll = 0.0

    print("Gun enabled before:", gun.enabled)
    gun.enabled = False
    print("Gun enabled after:", gun.enabled)

    for obj in [home_background, home_title, home_subtitle, primary_weapon_selector, home_join_button, home_host_button, home_settings_button, home_quit_button]:
        obj.enabled = False

    for obj in [
        menu_bg,
        menu_title,
        settings_button,
        leave_button, 
        name_label,
        name_input,
        height_label, height_value, height_slider,
        weight_label, weight_value, weight_slider, width_value,
    ]:
        obj.enabled = False

    for obj in [
        settings_bg,
        settings_title,
        settings_subtitle,
        settings_back_button,
    ]:
        obj.enabled = True

    for button in settings_tab_buttons.values():
        button.enabled = True

    refresh_settings()
    refresh_settings_tabs()

    mouse.locked = False
    mouse.visible = True

def back_to_menu():
    if settings_return_screen == "home":
        gun.enabled = False
        show_home_screen()
    else:
        show_menu()

def open_pause_settings():
    global settings_return_screen
    settings_return_screen = "pause"
    show_settings()

settings_button.on_click = open_pause_settings
settings_back_button.on_click = back_to_menu
leave_button.on_click = leave_game

# ============================================================
# HOME MENU / JOIN BROWSER / HOST LOBBY
# ============================================================

menu_screen = "home"
menu_status = "Choose an option to begin."
join_rows = []
last_join_signature = None
lobby_text = None

# Full-screen opaque menu keeps the arena hidden until a match starts.
home_background = Entity(
    parent=camera.ui, model="quad", color=color.azure,
    scale=(2, 2), position=(0, 0, 10), shader=unlit_shader,
)
home_title = Text(
    parent=camera.ui, text="LOCAL NETWORK FPS", origin=(0, 0),
    y=0.32, scale=2.2, color=color.white, z=-11,
)
home_subtitle = Text(
    parent=camera.ui, text="FOUR PLAYER ARENA", origin=(0, 0),
    y=0.23, scale=0.9, color=color.cyan, z=-11,
)


name_label.enabled = True
name_input.enabled = True

name_label.position = (0, 0.04)
name_label.origin = (0, 0)

name_input.position = (0, -0.04)
name_input.origin = (0, 0)

def format_height(inches):
    total_sixteenths = round(inches * 16)

    feet = total_sixteenths // 192
    remaining = total_sixteenths % 192

    whole_inches = remaining // 16
    fraction = Fraction(remaining % 16, 16)

    if fraction:
        return f"{feet}'{whole_inches} {fraction}\""

    return f"{feet}'{whole_inches}\""


def format_weight(pounds):
    total_sixteenths_oz = round(pounds * 256)

    whole_pounds = total_sixteenths_oz // 256
    remaining = total_sixteenths_oz % 256

    whole_ounces = remaining // 16
    fraction = Fraction(remaining % 16, 16)

    if remaining == 0:
        return f"{whole_pounds} lb"

    if whole_ounces == 0 and fraction:
        return f"{whole_pounds} lb {fraction} oz"

    if fraction:
        return f"{whole_pounds} lb {whole_ounces} {fraction} oz"

    return f"{whole_pounds} lb {whole_ounces} oz"

# Character size controls on the home screen.
height_label = Text(parent=camera.ui, text="HEIGHT", position=(-0.62, 0.045), scale=0.75, color=color.smoke, z=-11)
height_value = Text(parent=camera.ui, text=f"{character_height} in", position=(-0.45, -0.01), scale=0.75, color=color.smoke, z=-11)
height_slider = Slider(parent=camera.ui, min=MIN_HEIGHT, max=MAX_HEIGHT, default=character_height, step=1/192, x=-0.75, y=-0.015, scale=0.5, z=-11)
height_slider.bg.color = color.smoke
weight_label = Text(parent=camera.ui, text="WEIGHT", position=(-0.62, -0.085), scale=0.75, color=color.smoke, z=-11)
weight_value = Text(parent=camera.ui, text=f"{character_weight} lb", position=(-0.45, -0.14), scale=0.75, color=color.smoke, z=-11)
weight_slider = Slider(parent=camera.ui, min=MIN_WEIGHT, max=MAX_WEIGHT, default=character_weight, step=1/256, x=-0.75, y=-0.145, scale=0.5, color=color.smoke, z=-11)
weight_slider.bg.color = color.smoke
width_value = Text(parent=camera.ui, text="", position=(-0.68, -0.2), scale=0.65, color=color.white, z=-11)

def update_character_controls():
    global character_height, character_weight, player_max_hp, player_health

    character_height = round(height_slider.value * 16) / 16
    character_weight = round(weight_slider.value * 256) / 256

    width = calculate_character_width(character_height, character_weight)

    height_value.text = format_height(character_height)
    weight_value.text = format_weight(character_weight)

    width_value.text = (
        f"Max health: {calculate_max_hp(character_weight, character_height)} HP"
    )

    local_state["height"] = character_height
    local_state["weight"] = character_weight

    player_max_hp = calculate_effective_max_health(
        calculate_max_hp(character_weight, character_height)
    )

    if not session_started:
        player_health = player_max_hp

update_character_controls()

def home_button(label, y, callback):
    b = Button(
        parent=camera.ui, text=label, position=(0.55, y),
        scale=(0.38, 0.085), color=color.dark_gray,
        highlight_color=color.azure, pressed_color=color.white,
        text_color=color.white, z=-11,
    )
    b.on_click = callback
    return b

home_join_button = home_button("PLAY", 0.08, lambda: auto_play())
home_host_button = home_button("HOST GAME", 0.00, lambda: host_from_menu())
home_settings_button = home_button("SETTINGS", -0.12, lambda: open_home_settings())
home_quit_button = home_button("QUIT", -0.24, application.quit)

home_host_button.enabled = False

join_title = Text(parent=camera.ui, text="FIND A GAME", origin=(0,0), y=0.34, scale=1.7, color=color.white, z=-11, enabled=False)
join_hint = Text(parent=camera.ui, text="Searching your local Wi-Fi network...", origin=(0,0), y=0.25, scale=0.8, color=color.light_gray, z=-11, enabled=False)
join_back_button = Button(parent=camera.ui, text="BACK", position=(-0.55,-0.36), scale=(0.25,0.07), enabled=False, z=-11)
join_refresh_button = Button(parent=camera.ui, text="REFRESH", position=(0.55,-0.36), scale=(0.25,0.07), enabled=False, z=-11)
join_back_button.on_click = lambda: show_home_screen()
join_refresh_button.on_click = lambda: refresh_game_search()

lobby_title = Text(parent=camera.ui, text="HOST LOBBY", origin=(0,0), y=0.34, scale=1.7, color=color.white, z=-11, enabled=False)
lobby_players_text = Text(parent=camera.ui, text="", origin=(0,0), y=0.05, scale=1.0, color=color.white, z=-11, enabled=False)
lobby_start_button = Button(parent=camera.ui, text="START MATCH", position=(0.35,-0.34), scale=(0.32,0.08), enabled=False, z=-11)
lobby_back_button = Button(parent=camera.ui, text="BACK", position=(-0.48,-0.34), scale=(0.25,0.08), enabled=False, z=-11)
lobby_start_button.on_click = lambda: begin_match()
lobby_back_button.on_click = lambda: show_home_screen()

# ============================================================
# PRIMARY WEAPON + MODIFIER LOADOUT SELECTOR
# ============================================================

primary_weapon_selector = Entity(parent=camera.ui, enabled=False)
primary_weapon_menu_open = False
primary_weapon_choice_tiles = []
modifier_choice_tiles = []

SELECTED_WEAPON_Y = -0.36
WEAPON_TILE_SIZE = 0.08
WEAPON_TILE_GAP = 0.02
WEAPON_SLOT_SPACING = WEAPON_TILE_SIZE + WEAPON_TILE_GAP
PRIMARY_SLOT_X = -WEAPON_SLOT_SPACING
SECONDARY_SLOT_X = 0.0
MODIFIER_SLOT_X = WEAPON_SLOT_SPACING


def get_primary_weapon(weapon_id):
    return next(weapon for weapon in PRIMARY_WEAPONS if weapon["id"] == weapon_id)


def get_modifier(modifier_id):
    return next(modifier for modifier in MODIFIERS if modifier["id"] == modifier_id)


def get_modifier_name(modifier_id):
    if modifier_id is None:
        return "Unknown"
    return get_modifier(modifier_id)["name"]


def create_slot_caption(label, x):
    return Text(
        parent=primary_weapon_selector, text=label, origin=(0, 0),
        position=(x, SELECTED_WEAPON_Y - WEAPON_TILE_SIZE / 2 - 0.018, -0.1),
        scale=0.6, color=color.white,
    )


def create_empty_slot_tile(x, y):
    tile = Entity(
        parent=primary_weapon_selector, model="quad",
        color=color.rgba(40, 40, 40, 255),
        position=(x, y, -0.1), scale=(WEAPON_TILE_SIZE, WEAPON_TILE_SIZE),
        collider="box",
    )
    Entity(parent=tile, model="quad", color=color.rgba(0, 0, 0, 220),
           position=(0, -0.39, -0.02), scale=(1, 0.25))
    Text(parent=tile, text="EMPTY", origin=(0, 0),
         position=(0, -0.39, -0.04), scale=1.5, color=color.light_gray)
    return tile


# Secondary slot remains an empty placeholder.
create_empty_slot_tile(SECONDARY_SLOT_X, SELECTED_WEAPON_Y)
create_slot_caption("PRIMARY", PRIMARY_SLOT_X)
create_slot_caption("SECONDARY", SECONDARY_SLOT_X)
create_slot_caption("MODIFIERS", MODIFIER_SLOT_X)


def create_picture_tile(item, x, y, selected=False, item_type="weapon"):
    texture = load_texture(item["image"]) if item.get("image") else None
    tile = Entity(
        parent=primary_weapon_selector, model="quad", texture=texture,
        color=color.white, position=(x, y, -0.1),
        scale=(WEAPON_TILE_SIZE, WEAPON_TILE_SIZE), collider="box",
    )
    Entity(parent=tile, model="quad", color=color.rgba(0, 0, 0, 220),
           position=(0, -0.39, -0.02), scale=(1, 0.25))
    Text(parent=tile, text=item["name"].upper(), origin=(0, 0),
         position=(0, -0.39, -0.04), scale=1.5, color=color.white)

    if item_type == "weapon":
        tile.on_click = toggle_primary_weapon_menu if selected else (
            lambda item_id=item["id"]: choose_primary_weapon(item_id)
        )
    else:
        tile.on_click = toggle_modifier_menu if selected else (
            lambda item_id=item["id"]: choose_modifier(item_id)
        )
    return tile


# The modifier slot is created by update_modifier_selection_ui() below.

def close_primary_weapon_menu():
    global primary_weapon_menu_open
    primary_weapon_menu_open = False
    update_weapon_selection_ui()


def toggle_primary_weapon_menu():
    global primary_weapon_menu_open, modifier_menu_open, modifier_multiplier_open
    modifier_menu_open = False
    modifier_multiplier_open = False
    modifier_multiplier_panel.enabled = False
    update_modifier_selection_ui()
    primary_weapon_menu_open = not primary_weapon_menu_open
    update_weapon_selection_ui()


def choose_primary_weapon(weapon_id):
    select_weapon(weapon_id)
    close_primary_weapon_menu()


def update_weapon_selection_ui():
    for tile in primary_weapon_choice_tiles:
        destroy(tile)
    primary_weapon_choice_tiles.clear()
    if hasattr(update_weapon_selection_ui, "selected_tile"):
        destroy(update_weapon_selection_ui.selected_tile)

    update_weapon_selection_ui.selected_tile = create_picture_tile(
        get_primary_weapon(current_weapon), PRIMARY_SLOT_X, SELECTED_WEAPON_Y,
        selected=True, item_type="weapon",
    )

    if not primary_weapon_menu_open:
        return

    available = [w for w in PRIMARY_WEAPONS if w["id"] != current_weapon]
    spacing = WEAPON_TILE_SIZE + WEAPON_TILE_GAP
    total_width = len(available) * WEAPON_TILE_SIZE + max(0, len(available)-1) * WEAPON_TILE_GAP
    start_x = PRIMARY_SLOT_X - total_width / 2 + WEAPON_TILE_SIZE / 2
    for index, weapon in enumerate(available):
        tile = create_picture_tile(
            weapon, start_x + index * spacing,
            SELECTED_WEAPON_Y + WEAPON_TILE_SIZE + 0.03,
            item_type="weapon",
        )
        primary_weapon_choice_tiles.append(tile)


# Multiplier panel is mutually exclusive with both selection menus.
modifier_multiplier_panel = Entity(parent=primary_weapon_selector, enabled=False)
modifier_multiplier_title = Text(
    parent=modifier_multiplier_panel, text="MODIFIER MULTIPLIER",
    origin=(0, 0), position=(0, 0.12), scale=1, color=color.white,
)

modifier_multiplier_value = Text(
    parent=modifier_multiplier_panel, text="1.00x",
    origin=(0, 0), position=(0, 0.04), scale=0.9, color=color.azure,
)

modifier_multiplier_slider = Slider(
    parent=modifier_multiplier_panel,
    min=MODIFIER_MIN,
    max=MODIFIER_MAX,
    default=1.0,
    step=0.01,
    x=0,
    y=-0.27,
    scale=(0.4, 0.6, 1),
)
modifier_multiplier_slider.bg.color = color.gray

modifier_multiplier_text = Text(
    parent=modifier_multiplier_panel,
    text="x1.00",
    origin=(0, 0),
    position=(MODIFIER_SLOT_X, -0.30, -0.1),
    scale=(0.4, 0.6, 1),
    color=color.white,
)

def update_modifier_multiplier():
    global modifier_multiplier

    modifier_multiplier = round(modifier_multiplier_slider.value, 2)

    # Update the text above the slider.
    modifier_multiplier_value.text = f"{modifier_multiplier:.2f}x"

    # Update the text below the slider.
    modifier_multiplier_text.text = f"x{modifier_multiplier:.2f}"

modifier_multiplier_slider.on_value_changed = update_modifier_multiplier


def close_modifier_multiplier():
    global modifier_multiplier_open
    modifier_multiplier_open = False
    modifier_multiplier_panel.enabled = False


def close_modifier_menu():
    global modifier_menu_open
    modifier_menu_open = False
    update_modifier_selection_ui()


def open_modifier_multiplier():
    global primary_weapon_menu_open, modifier_menu_open, modifier_multiplier_open
    if selected_modifier is None:
        return
    primary_weapon_menu_open = False
    modifier_menu_open = False
    update_weapon_selection_ui()
    update_modifier_selection_ui()
    modifier_multiplier_open = True
    modifier_multiplier_panel.enabled = True
    modifier_multiplier_title.text = f"{get_modifier_name(selected_modifier).upper()} MULTIPLIER"
    modifier_multiplier_slider.value = modifier_multiplier
    update_modifier_multiplier()


def toggle_modifier_menu():
    global modifier_menu_open, primary_weapon_menu_open, modifier_multiplier_open
    primary_weapon_menu_open = False
    modifier_multiplier_open = False
    modifier_multiplier_panel.enabled = False
    update_weapon_selection_ui()
    modifier_menu_open = not modifier_menu_open
    update_modifier_selection_ui()


def choose_modifier(modifier_id):
    global selected_modifier, modifier_multiplier, modifier_menu_open
    selected_modifier = modifier_id
    modifier_multiplier = 1.0
    modifier_multiplier_slider.value = 1.0
    modifier_menu_open = False
    update_modifier_selection_ui()


def update_modifier_selection_ui():
    for tile in modifier_choice_tiles:
        destroy(tile)
    modifier_choice_tiles.clear()

    if hasattr(update_modifier_selection_ui, "selected_tile"):
        destroy(update_modifier_selection_ui.selected_tile)

    if selected_modifier is None:
        selected_tile = create_empty_slot_tile(MODIFIER_SLOT_X, SELECTED_WEAPON_Y)
        selected_tile.on_click = toggle_modifier_menu
        update_modifier_selection_ui.selected_tile = selected_tile
    else:
        update_modifier_selection_ui.selected_tile = create_picture_tile(
            get_modifier(selected_modifier), MODIFIER_SLOT_X,
            SELECTED_WEAPON_Y, selected=True, item_type="modifier",
        )

    if not modifier_menu_open:
        return

    available = [m for m in MODIFIERS if m["id"] != selected_modifier]
    spacing = WEAPON_TILE_SIZE + WEAPON_TILE_GAP
    total_width = len(available) * WEAPON_TILE_SIZE + max(0, len(available)-1) * WEAPON_TILE_GAP
    start_x = MODIFIER_SLOT_X - total_width / 2 + WEAPON_TILE_SIZE / 2
    for index, modifier in enumerate(available):
        tile = create_picture_tile(
            modifier, start_x + index * spacing,
            SELECTED_WEAPON_Y + WEAPON_TILE_SIZE + 0.03,
            item_type="modifier",
        )
        modifier_choice_tiles.append(tile)


# Right-clicking the equipped modifier opens its multiplier controls.
def input_modifier_right_click(key):
    if key == "right mouse down" and primary_weapon_selector.enabled:
        target = mouse.hovered_entity
        selected_tile = getattr(update_modifier_selection_ui, "selected_tile", None)
        if selected_tile is not None and target == selected_tile and selected_modifier is not None:
            open_modifier_multiplier()
            return True
    return False


# Initial setup.
update_weapon_selection_ui()
update_modifier_selection_ui()
update_modifier_multiplier()

def hide_all_frontend():
    close_primary_weapon_menu()
    close_modifier_menu()
    close_modifier_multiplier()

    for obj in [
        menu_bg, menu_title, settings_button, leave_button,
        home_background, home_title, home_subtitle,
        home_join_button, home_host_button,
        home_settings_button, home_quit_button,
        join_title, join_hint, join_back_button, 
        join_refresh_button, lobby_title, lobby_players_text,
        lobby_start_button, lobby_back_button,
        primary_weapon_selector, height_label, height_value, height_slider,
        weight_label, weight_value, weight_slider, width_value,
    ]:
        obj.enabled = False

    for row in join_rows:
        for obj in row:
            destroy(obj)
    join_rows.clear()

def show_home_screen():
    global menu_screen, menu_open, settings_open, discovery_active
    global auto_play_active

    menu_screen = "home"
    menu_open = True
    settings_open = False
    discovery_active = False
    auto_play_active = False

    hide_all_frontend()

    # Clear the Settings screen before restoring the home screen.
    for obj in [
        settings_bg, settings_title, settings_subtitle,
        sprint_toggle, crouch_toggle, settings_back_button,
    ]:
        obj.enabled = False

    for label in slider_labels:
        label.enabled = False

    for slider, value_text, key in slider_objects:
        slider.enabled = False
        value_text.enabled = False
    hide_settings_widgets()
        
    for obj in [
        home_background, home_title, home_subtitle,
        home_join_button, home_host_button,
        home_settings_button, home_quit_button,
        name_label, name_input,
        height_label, height_value, height_slider,
        weight_label, weight_value, weight_slider, width_value,
        primary_weapon_selector
    ]:
        obj.enabled = True

    name_label.position = (0, 0.04)
    name_label.origin = (0, 0)

    name_input.position = (0, -0.04)
    name_input.origin = (0, 0)

    home_join_button.enabled = True
    home_host_button.enabled = False
    home_settings_button.enabled = True
    home_quit_button.enabled = True

    mouse.locked = False
    mouse.visible = True

def open_client_lobby():
    global menu_screen, menu_open, settings_open

    menu_screen = "lobby"
    menu_open = True
    settings_open = False

    hide_all_frontend()

    for obj in [height_label, height_value, height_slider, weight_label, weight_value, weight_slider, width_value, name_label, name_input]:
        obj.enabled = False

    for obj in [home_background, lobby_title, lobby_players_text, lobby_back_button, primary_weapon_selector]:
        obj.enabled = True

    lobby_title.text = "GAME LOBBY"
    update_lobby_display()

    mouse.locked = False
    mouse.visible = True

def open_join_screen():
    global menu_screen, menu_open, settings_open

    if network_ready:
        open_client_lobby()
        return
    
    menu_screen = "join"
    menu_open = True
    settings_open = False
    hide_all_frontend()
    name_label.enabled = False
    name_input.enabled = False
    for obj in (height_label, height_value, height_slider, weight_label, weight_value, weight_slider, width_value): obj.enabled = False
    for obj in [home_background, join_title, join_hint, join_back_button, join_refresh_button]:
        obj.enabled = True
    join_hint.text = "Searching your local Wi-Fi network..."
    begin_discovery()
    mouse.locked = False
    mouse.visible = True

def begin_discovery():
    global discovery_active, last_discovery

    if network_ready:
        join_hint.text = "Already connected to a game."
        return

    reset_network_socket()

    try:
        net.bind(("", 0))
        discovery_active = True
        last_discovery = 0.0
        discovered_games.clear()
        send_game_discovery()
        last_discovery = time.time()

    except OSError as error:
        discovery_active = False
        join_hint.text = f"Search failed: {error}"

auto_play_active = False
auto_play_deadline = 0.0


def auto_play():
    global player_name
    global auto_play_active, auto_play_deadline

    if network_ready or auto_play_active:
        return

    player_name = name_input.text.strip() or "Player"
    update_character_controls()

    local_state["name"] = player_name
    local_state["height"] = character_height
    local_state["weight"] = character_weight

    discovered_games.clear()

    home_join_button.enabled = False
    home_settings_button.enabled = False
    home_quit_button.enabled = False

    begin_discovery()

    if not discovery_active:
        home_join_button.enabled = True
        home_settings_button.enabled = True
        home_quit_button.enabled = True
        return

    auto_play_active = True
    auto_play_deadline = time.time() + 2.5


def finish_auto_play():
    global auto_play_active

    if not auto_play_active:
        return

    auto_play_active = False
    discovery_active = False

    if discovered_games:
        # Join the first available host.
        address = next(iter(discovered_games))
        join_selected_game(address)

    else:
        start_host()

        if network_ready:
            begin_match()
        else:
            home_join_button.enabled = True
            home_settings_button.enabled = True
            home_quit_button.enabled = True

def refresh_game_search():
    global last_discovery, last_join_signature
    discovered_games.clear()
    last_join_signature = None
    for row in join_rows:
        for obj in row:
            destroy(obj)
    join_rows.clear()
    join_hint.text = "Searching again..."
    last_discovery = 0.0

def refresh_join_rows():
    global last_join_signature
    if menu_screen != "join":
        return
    signature = tuple(sorted((str(addr), info.get("name"), info.get("count"), info.get("max")) for addr, info in discovered_games.items()))
    if signature == last_join_signature:
        return
    last_join_signature = signature
    for row in join_rows:
        for obj in row:
            destroy(obj)
    join_rows.clear()
    if not discovered_games:
        join_hint.text = "No games found yet. Make sure the host is on the same Wi-Fi."
        return
    join_hint.text = "Select a game to join:"
    for index, (address, info) in enumerate(list(discovered_games.items())[:8]):
        y = 0.14 - index * 0.075
        label = f"{info['name']}  |  {info['count']}/{info['max']} players  |  {address[0]}"
        b = Button(parent=camera.ui, text=label, position=(0, y), scale=(0.72,0.06),
                   color=color.dark_gray, highlight_color=color.azure, z=-11)
        b.on_click = (lambda addr=address: join_selected_game(addr))
        join_rows.append([b])

def join_selected_game(address):
    global player_name

    player_name = name_input.text.strip() or "Player"
    update_character_controls()
    hide_all_frontend()

    home_background.enabled = True
    join_title.enabled = True
    join_title.text = "CONNECTING..."
    join_hint.enabled = True
    join_hint.text = f"Connecting to {address[0]}..."

    connect_to_discovered_game(address)

def host_from_menu():
    global player_name
    player_name = name_input.text.strip() if name_input.text.strip() else "Host"
    update_character_controls()
    local_state["name"] = player_name
    local_state["height"] = character_height
    local_state["weight"] = character_weight
    start_host()
    if network_ready:
        open_host_lobby()
    else:
        pass

def open_host_lobby():
    global menu_screen, menu_open, settings_open
    menu_screen = "lobby"
    menu_open = True
    settings_open = False
    hide_all_frontend()
    name_label.enabled = False
    name_input.enabled = False
    for obj in (height_label, height_value, height_slider, weight_label, weight_value, weight_slider, width_value): obj.enabled = False

    for obj in [
        home_background,
        lobby_title,
        lobby_players_text,
        lobby_start_button,
        lobby_back_button,
        primary_weapon_selector
    ]:
        obj.enabled = True
        obj.enabled = True
    update_lobby_display()
    mouse.locked = False
    mouse.visible = True
    

def update_lobby_display():
    if menu_screen != "lobby":
        return
    rows = []
    for pid, info in sorted(players.items()):
        rows.append(f"PLAYER {pid}:  {info.get('name', 'Player')}")
    lobby_players_text.text = "\n".join(rows) + f"\n\n{len(players)}/{MAX_PLAYERS} PLAYERS"
    lobby_start_button.enabled = is_host and len(players) >= 1

def begin_match():
    global session_started, menu_open, settings_open, menu_screen
    global player_max_hp, player_health, start_x, start_z
    global has_left

    has_left = False

    build_arena(random.randint(0, 2**31 - 1))

    start_x, start_z = find_valid_spawn(
        character_height,
        character_weight,
    )

    local_state["x"] = start_x
    local_state["z"] = start_z

    player_max_hp = calculate_effective_max_health(
        calculate_max_hp(character_weight, character_height)
    )
    player_health = player_max_hp

    local_body.position = (
        start_x,
        character_height / 2,
        start_z,
    )

    camera.position = (
        start_x,
        STAND_EYE_HEIGHT,
        start_z,
    )

    update_health_ui()
    hide_all_frontend()

    menu_open = False
    settings_open = False
    session_started = True
    menu_screen = "game"

    for obj in [
        menu_bg, menu_title, settings_button, name_label, name_input,
        settings_bg, settings_title, settings_subtitle,
        sprint_toggle, crouch_toggle, settings_back_button,
        player_list_bg, player_list_title, player_list_headers,
        player_list_text, chat_input, chat_display,
        reticle, reticle_dot, health_text,
        remote_health_text, ammo_weapon_text, gun,
    ]:
        obj.enabled = False

    for label in slider_labels:
        label.enabled = False

    for slider, value_text, key in slider_objects:
        slider.enabled = False
        value_text.enabled = False
    hide_settings_widgets()

    for obj in [
        reticle, reticle_dot, health_text,
        remote_health_text, ammo_weapon_text, gun,
    ]:
        obj.enabled = True

    mouse.locked = True
    mouse.visible = False

    if is_host:
        broadcast_packet({"type": "match_start"})

def open_home_settings():
    global settings_return_screen
    settings_return_screen = "home"
    for obj in [home_background, home_title, home_subtitle, home_join_button, home_host_button, home_settings_button, home_quit_button, name_label, name_input, height_label, height_value, height_slider, weight_label, weight_value, weight_slider, width_value]:
        obj.enabled = False
    show_settings()

settings_return_screen = "pause"

def update_frontend():
    global auto_play_active

    if auto_play_active:
        if discovered_games:
            finish_auto_play()
        elif time.time() >= auto_play_deadline:
            finish_auto_play()

    if menu_screen == "join":
        refresh_join_rows()

    elif menu_screen == "lobby":
        update_lobby_display()

# Initial state: gameplay stays behind the independent home screen.
show_home_screen()
for _frontend_hidden in [menu_bg, menu_title, settings_button,
                         player_list_bg, player_list_title, player_list_headers, player_list_text,
                         reticle, reticle_dot, health_text, remote_health_text, ammo_weapon_text, gun]:
    _frontend_hidden.enabled = False


# ============================================================
# CHAT
# ============================================================

chat_messages = []

chat_input = InputField(
    parent=camera.ui,
    y=-0.35,
    scale=(0.7, 0.05),
    enabled=False,
    visible=False,
)

chat_display = Text(
    parent=camera.ui,
    text="",
    position=(-0.85, -0.25),
    scale=0.8,
    color=TEXT_MAIN,
)


# ============================================================
# UPDATE
# ============================================================

def update():
    global pitch, yaw, last_send, client_address
    global is_aiming, is_crouching
    global recoil_pitch, recoil_yaw, ak_recoil_active, ak_shots
    global player_health, remote_health, remote_respawn_at
    global vertical_velocity, is_grounded
    global last_discovery
    
    dt = min(time.dt, 0.05)
    now = time.time()

    # LAN networking and front-end screens remain active before the match.
    process_network()
    update_frontend()
    if menu_screen == "home":
        update_character_controls()

    if discovery_active and now - last_discovery >= 1.0:
        send_game_discovery()
        last_discovery = now

    # Advance reloads. Single-shell weapons add one round per reload_time.
    for name, weapon in WEAPONS.items():
        state = reload_state[name]
        if not state["active"]:
            continue
        if weapon["reload_type"] == "single":
            if now >= state["next_shell"]:
                ammo_in_mag[name] = min(weapon["mag"], ammo_in_mag[name] + 1)
                if ammo_in_mag[name] >= weapon["mag"]:
                    state["active"] = False
                    reload_end_time[name] = 0.0
                    if name == current_weapon:
                        print(f"Finished reloading {name}")
                else:
                    state["next_shell"] += calculate_effective_reload_time(weapon["reload_speed"])
                    reload_end_time[name] = state["next_shell"]
                if name == current_weapon:
                    update_health_ui()
        elif reload_end_time[name] > 0 and now >= reload_end_time[name]:
            ammo_in_mag[name] = weapon["mag"]
            reload_end_time[name] = 0.0
            state["active"] = False
            if name == current_weapon:
                update_health_ui()
                print(f"Finished reloading {name}")

    if modifier_multiplier_open:
        update_modifier_multiplier()
        
    # Reticle visibility.
    reticle.enabled = (
        settings["reticle_outline"]
        and not menu_open and not settings_open and not chat_open
        and player_health > 0
    )

    reticle_dot.enabled = (
        settings["reticle_inside"]
        and not menu_open and not settings_open and not chat_open
        and player_health > 0
    )

    advance_recoil(dt)

    # Bullets and effects only run during an active match.
    if session_started and not menu_open:
        update_bullets(dt)

    update_explosions(dt)

    # Local player respawn.
    if (
        session_started
        and not has_left
        and local_respawn_at
        and now >= local_respawn_at
    ):
        global_local_respawn()
        
    # Remote player respawn.
    if (
        session_started
        and not has_left
        and remote_respawn_at
        and now >= remote_respawn_at
    ):
        global_remote_respawn()

    # Automatic primary-weapon fire.
    if (
        WEAPONS[current_weapon]["mode"] == "automatic"
        and action_held("fire")
        and not has_left
        and not menu_open
        and not chat_open
        and player_health > 0
    ):
        shoot()

    # Update settings sliders.
    for slider, value_text, key in slider_objects:
        value = int(slider.value)
        settings[key] = value
        value_text.text = str(value)

    camera.fov = settings["fov"]
    reticle.color = color.rgb(
        settings["reticle_outline_r"],
        settings["reticle_outline_g"],
        settings["reticle_outline_b"],
    )
    reticle_dot.color = color.rgb(
        settings["reticle_inside_r"],
        settings["reticle_inside_g"],
        settings["reticle_inside_b"],
    )
    reticle.scale = 0.004 + settings["reticle_border_size"] * 0.001

    is_aiming = (
        action_held("aim")
        and not menu_open
        and not chat_open
        and player_health > 0
    )

    if settings["sprint_mode"] == "Hold":
        is_sprinting = action_held("sprint")
    else:
        is_sprinting = sprint_toggled

    if settings["crouch_mode"] == "Hold":
        crouch_active = action_held("crouch")
    else:
        crouch_active = crouch_toggled

    if menu_open or chat_open or player_health <= 0:
        is_sprinting = False
        crouch_active = False

    is_crouching = crouch_active

    # Player movement and camera control.
    if (
        session_started
        and not menu_open
        and not has_left
        and not settings_open
        and not chat_open
        and player_health > 0
    ):
        sx = (
            settings["ads_sens_x"]
            if is_aiming
            else settings["sens_x"]
        )

        sy = (
            settings["ads_sens_y"]
            if is_aiming
            else settings["sens_y"]
        )

        yaw += mouse.velocity[0] * sx
        pitch -= mouse.velocity[1] * sy
        pitch = clamp(pitch, -85, 85)

        forward = Vec3(
            math.sin(math.radians(yaw)),
            0,
            math.cos(math.radians(yaw)),
        )

        right = Vec3(
            forward.z,
            0,
            -forward.x,
        )

        move = Vec3(0, 0, 0)

        if action_held("move_forward"):
            move += forward

        if action_held("move_back"):
            move -= forward

        if action_held("move_right"):
            move += right

        if action_held("move_left"):
            move -= right

        if move.length() > 0:
            move = move.normalized()

        if is_crouching and is_sprinting:

            crouch_speed = calculate_movement_speed(
                character_height, character_weight, "crouch"
            )

            sprint_speed = calculate_movement_speed(
                character_height, character_weight, "sprint"
            )

            speed = (crouch_speed + sprint_speed) / 2

        elif is_crouching:

            speed = calculate_movement_speed(
                character_height, character_weight, "crouch"
            )

        elif is_sprinting:

            speed = calculate_movement_speed(
                character_height, character_weight, "sprint"
            )

        else:

            speed = calculate_movement_speed(
                character_height, character_weight, "walk"
            )

        speed = calculate_effective_speed(speed)

        # Move on X only if the new position is clear
        new_x = local_state["x"] + move.x * speed * dt

        if not position_blocked(new_x, local_state["z"]):
            local_state["x"] = new_x

        # Move on Z only if the new position is clear
        new_z = local_state["z"] + move.z * speed * dt

        if not position_blocked(local_state["x"], new_z):
            local_state["z"] = new_z

        # JUMPING
        eye_height = (
            CROUCH_EYE_HEIGHT
            if is_crouching
            else STAND_EYE_HEIGHT
        )

        if action_held("jump") and is_grounded:
            jump_height = calculate_jump_height(
                character_height, character_weight
            )

            effective_gravity = calculate_effective_gravity()
            vertical_velocity = math.sqrt(2 * effective_gravity * jump_height)
            is_grounded = False

        effective_gravity = calculate_effective_gravity()
        vertical_velocity -= effective_gravity * dt

        camera_y = camera.position.y + vertical_velocity * dt

        if camera_y <= eye_height:
            camera_y = eye_height
            vertical_velocity = 0.0
            is_grounded = True

        camera.position = (
            local_state["x"],
            camera_y,
            local_state["z"],
        )

        local_state["x"] = clamp(
            local_state["x"],
            -ARENA_HALF + WALL_THICKNESS + calculate_character_width(character_height, character_weight),
            ARENA_HALF - WALL_THICKNESS - calculate_character_width(character_height, character_weight),
        )

        local_state["z"] = clamp(
            local_state["z"],
            -ARENA_HALF + WALL_THICKNESS + calculate_character_width(character_height, character_weight) * 0.75,
            ARENA_HALF - WALL_THICKNESS - calculate_character_width(character_height, character_weight) * 0.75,
        )

    local_state["yaw"] = yaw
    local_state["pitch"] = pitch
    local_state["name"] = player_name

    eye_height = (
        CROUCH_EYE_HEIGHT
        if is_crouching and player_health > 0
        else STAND_EYE_HEIGHT
    )

    camera.position = (
        local_state["x"],
        camera.position.y,
        local_state["z"],
    )

    local_body.position = (
        local_state["x"],
        PLAYER_HEIGHT / 2,
        local_state["z"],
    )

    camera.rotation = (clamp(pitch, -85, 85), yaw, 0)

    gun_base_position = (0, -0.18, 0.45) if is_aiming else (0.32, -0.28, 0.65)

    visual_recoil = recoil_patterns.setdefault(
        current_weapon,
        {
            "index": 0,
            "elapsed": 0.0,
            "last_release": 0.0,
            "gun_x": 0.0,
            "gun_y": 0.0,
        }
    )

    # Keep the weapon in its original position.
    gun.position = gun_base_position

    # Rotate the weapon upward during recoil.
    gun.rotation = (
        -visual_recoil["gun_y"] * 18,
        visual_recoil["gun_x"] * 18,
        0,
    )

    # Send current position and receive LAN packets through one network loop.
    if session_started and not has_left:
        network_update()

    # The new four-player entities replace the old single-opponent model.
    if not has_left:
        for pid, state_info in players.items():
            if pid == player_number:
                continue
            update_player_entity(pid, state_info.get("state", {}))

    # ------------------------------------------------------------
    # PLAYER LIST
    # ------------------------------------------------------------

    show_player_list = (
        action_held("player_list")
        and not menu_open
        and not settings_open
        and not chat_open
    )

    display_players = []
    for pid, info in sorted(players.items()):
        display_name = info.get("name", f"Player {pid}")
        display_players.append((display_name, "IN GAME"))

    if not display_players:
        display_players.append((player_name, "LOBBY"))
    # Calculate the height based on the number of players.
    row_height = 0.045
    header_height = 0.07
    total_height = header_height + len(display_players) * row_height

    player_list_bg.scale = (0.55, total_height)
    player_list_bg.position = (0, 0, 0)

    player_list_title.position = (
        0, total_height / 2 - 0.035, -1
    )

    player_list_headers.position = (
        0, total_height / 2 - 0.075, -1
    )

    player_list_text.position = (
        0, total_height / 2 - 0.11, -1
    )

    player_list_text.text = "\n".join(
        f"{name:<24} {status}"
        for name, status in display_players
    )

    player_list_bg.enabled = show_player_list
    player_list_title.enabled = show_player_list
    player_list_headers.enabled = show_player_list
    player_list_text.enabled = show_player_list

# ============================================================
# INPUT
# ============================================================

def input(key):
    global menu_open, chat_open, player_name
    global sprint_toggled, crouch_toggled
    global game_scroll

    name = press_event_name(key)

    if input_modifier_right_click(key):
        return

    if name in ("scroll up", "scroll down"):
        key_pulse[name] = time.time() + SCROLL_PULSE_SECONDS

    # Rebinding: the next key / mouse button press becomes the new bind.
    if bind_listen["target"] is not None:
        handle_bind_capture(name)
        return

    # Do not allow gameplay input while dead.
    if player_health <= 0:
        return


    # Scroll the whole Game settings list with the mouse wheel.
    if settings_open and settings_tab == "Game" and key in ("scroll up", "scroll down"):
        direction = 1 if key == "scroll down" else -1
        game_scroll = max(0.0, min(GAME_SCROLL_MAX, game_scroll + direction * GAME_SCROLL_STEP))
        apply_game_scroll(True)
        return

    action = action_for_key(name) if name else None

    if action == "sprint" and settings["sprint_mode"] == "Toggle":
        if not menu_open and not chat_open:
            sprint_toggled = not sprint_toggled
        return

    if action == "crouch" and settings["crouch_mode"] == "Toggle":
        if not menu_open and not chat_open:
            crouch_toggled = not crouch_toggled
        return

    if key == "escape":
        if chat_open:
            chat_open = False
            chat_input.enabled = False
            chat_input.visible = False

            mouse.locked = not menu_open
            mouse.visible = menu_open
            return

        if settings_open:
            back_to_menu()
            return

        if menu_open:
            if menu_screen == "pause":
                hide_menu()
            return

        else:
            if session_started:
                show_menu()

        return

    if menu_open:
        return

    # Single-character chat keys are typed into the box while it is open,
    # so they only open chat; Esc closes it.
    if action == "chat" and (not chat_open or len(name) > 1):
        chat_open = not chat_open

        chat_input.enabled = chat_open
        chat_input.visible = chat_open

        mouse.locked = not chat_open
        mouse.visible = chat_open

        if chat_open:
            chat_input.text = ""
            chat_input.active = True
            # Drop the key press that opened chat if it was typed in.
            invoke(setattr, chat_input, "text", "", delay=0.03)

        return

    if chat_open:
        if key == "enter":
            message = chat_input.text.strip()

            if message:
                chat_messages.append(f"You: {message}")
                chat_messages[:] = chat_messages[-5:]
                chat_display.text = "\n".join(chat_messages)

            chat_input.text = ""
            chat_input.active = True

        return

    if action == "reload":
        reload_weapon()
        return

    if action == "fire" and WEAPONS[current_weapon]["mode"] != "automatic":
        shoot()
        return


app.run()
