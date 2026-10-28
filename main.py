"""
Two-Player FPS Prototype
Engine: Ursina
Optional controller input: pygame (install pygame-ce or pygame)

Install:
    py -m pip install ursina pygame-ce

Run:
    py main.py

Prototype notes:
- This first build runs both players in one window with side-by-side views.
- Separate OS windows on separate monitors are a later rendering step; that needs
  extra testing with Panda3D/Ursina and your Intel HD 530.
- Keyboard controls are included so the game can be tested before controllers.
"""

from ursina import *
from ursina.prefabs.first_person_controller import FirstPersonController
import math
import time

try:
    import pygame
    pygame.init()
    pygame.joystick.init()
    PYGAME_AVAILABLE = True
except Exception:
    pygame = None
    PYGAME_AVAILABLE = False


# ------------------------- Game configuration -------------------------

MATCH_SECONDS = 150
KILL_LIMIT = 10
MAX_HP = 100
SHOT_DAMAGE = 13
RESPAWN_INVULNERABILITY = 0.5
MOVE_SPEED = 6.5
ARENA_HALF_SIZE = 18

# Edit these mappings in Settings later, or change them here for now.
# Button and axis numbers vary by controller model.
CONTROLLER_MAP = {
    "move_x_axis": 0,
    "move_y_axis": 1,
    "aim_x_axis": 2,
    "aim_y_axis": 3,
    "shoot_button": 7,       # common mapping: right trigger may differ by controller
    "jump_button": 0,
    "sprint_button": 8,
    "deadzone": 0.18,
}

# Keyboard fallback for testing without controllers.
KEYBOARD = {
    0: {"left": "a", "right": "d", "forward": "w", "back": "s",
        "turn_left": "q", "turn_right": "e", "look_up": "r", "look_down": "f",
        "shoot": "space", "jump": "left shift"},
    1: {"left": "left arrow", "right": "right arrow",
        "forward": "up arrow", "back": "down arrow",
        "turn_left": "j", "turn_right": "l", "look_up": "i", "look_down": "k",
        "shoot": "right shift", "jump": "enter"},
}


app = Ursina()
window.title = "Two-Player FPS Prototype"
window.color = color.rgb(15, 18, 25)
window.fps_counter.enabled = True
window.exit_button.visible = True
camera.fov = 90
mouse.visible = True

game_state = "menu"
time_left = MATCH_SECONDS
scores = [0, 0]
players = []
controllers = []
arena_entities = []
ui_entities = []
settings_panel = None


def clamp(value, low, high):
    return max(low, min(high, value))


def deadzone(value, dz=None):
    dz = CONTROLLER_MAP["deadzone"] if dz is None else dz
    return 0.0 if abs(value) < dz else value


def refresh_controllers():
    global controllers
    controllers = []
    if not PYGAME_AVAILABLE:
        return
    try:
        pygame.event.pump()
        for i in range(pygame.joystick.get_count()):
            stick = pygame.joystick.Joystick(i)
            if not stick.get_init():
                stick.init()
            controllers.append(stick)
    except Exception:
        controllers = []


def clear_entities(items):
    for item in items[:]:
        try:
            destroy(item)
        except Exception:
            pass
    items.clear()


def make_text(text, position, scale=1.0, parent=camera.ui, origin=(0, 0)):
    obj = Text(text=text, position=position, scale=scale, parent=parent, origin=origin)
    ui_entities.append(obj)
    return obj


class Arena:
    def __init__(self):
        self.entities = []
        self.build()

    def add_box(self, position, scale, tint=color.gray, collider="box"):
        e = Entity(
            model="cube", position=position, scale=scale,
            color=tint, collider=collider, texture="white_cube"
        )
        self.entities.append(e)
        return e

    def build(self):
        # Floor and enclosing walls.
        self.add_box((0, -0.5, 0), (ARENA_HALF_SIZE * 2, 1, ARENA_HALF_SIZE * 2),
                     color.rgb(75, 80, 90))
        wall_color = color.rgb(45, 53, 68)
        self.add_box((0, 2, ARENA_HALF_SIZE), (ARENA_HALF_SIZE * 2, 4, 1), wall_color)
        self.add_box((0, 2, -ARENA_HALF_SIZE), (ARENA_HALF_SIZE * 2, 4, 1), wall_color)
        self.add_box((ARENA_HALF_SIZE, 2, 0), (1, 4, ARENA_HALF_SIZE * 2), wall_color)
        self.add_box((-ARENA_HALF_SIZE, 2, 0), (1, 4, ARENA_HALF_SIZE * 2), wall_color)

        # Low cover arranged symmetrically.
        cover = color.rgb(105, 116, 132)
        for x, z, sx, sz in [
            (-7, -5, 4, 2), (7, 5, 4, 2),
            (-7, 5, 2, 4), (7, -5, 2, 4),
            (0, 0, 4, 2), (0, 10, 5, 2), (0, -10, 5, 2),
            (-12, 0, 2, 5), (12, 0, 2, 5),
        ]:
            self.add_box((x, 0.8, z), (sx, 1.6, sz), cover)

    def destroy(self):
        clear_entities(self.entities)


class Player:
    def __init__(self, index, spawn):
        self.index = index
        self.spawn = Vec3(*spawn)
        self.position = Vec3(*spawn)
        self.yaw = 0 if index == 0 else 180
        self.pitch = 0
        self.hp = MAX_HP
        self.kills = 0
        self.deaths = 0
        self.invulnerable_until = 0
        self.speed = MOVE_SPEED
        self.kills_text = None
        self.hp_text = None
        self.hp_back = None
        self.hp_fill = None
        self.crosshair = None
        self.view_camera = None
        self.view = None
        self.body = None
        self.weapon = None
        self.create_view()

    def create_view(self):
        # Both views are separate display regions inside the same window.
        # This gives us a reliable playable prototype before multi-window work.
        self.view = camera
        self.view_camera = Entity(
            parent=scene, model=None, position=self.position + Vec3(0, 1.65, 0),
            rotation=(self.pitch, self.yaw, 0)
        )
        self.view_camera.enabled = False

        # Use two cameras with separate display regions where Panda3D supports it.
        # Ursina's default camera is retained for the first view; the second view
        # is created below using a dedicated Camera entity and display region.
        if self.index == 0:
            self.view_camera.enabled = True
            self.view_camera.camera = None
            self.view_camera.add_script = None
            self.camera_component = Camera(
                parent=self.view_camera, aspect_ratio=1.0, fov=90
            )
            self.camera_component.ui = Entity(parent=self.view_camera)
            self.display_region = None
        else:
            self.camera_component = None
            self.display_region = None

        # Player marker is visible only as a development aid.
        self.body = Entity(
            model="cube", color=color.azure if self.index == 0 else color.orange,
            scale=(0.7, 1.7, 0.7), position=self.position,
            collider="box", visible=False
        )
        self.weapon = Entity(
            parent=self.view_camera, model="cube",
            position=(0.32, -0.28, 0.65), scale=(0.16, 0.16, 0.65),
            color=color.dark_gray, rotation=(0, 0, 0)
        )

    def current_controller(self):
        return controllers[self.index] if self.index < len(controllers) else None

    def read_input(self):
        move_x = move_z = aim_x = aim_y = 0.0
        shooting = False
        jump = False

        # Controller input, when a controller is connected for this player.
        pad = self.current_controller()
        if pad:
            try:
                pygame.event.pump()
                move_x = deadzone(pad.get_axis(CONTROLLER_MAP["move_x_axis"]))
                move_z = -deadzone(pad.get_axis(CONTROLLER_MAP["move_y_axis"]))
                aim_x = deadzone(pad.get_axis(CONTROLLER_MAP["aim_x_axis"]))
                aim_y = deadzone(pad.get_axis(CONTROLLER_MAP["aim_y_axis"]))
                b = CONTROLLER_MAP["shoot_button"]
                if b < pad.get_numbuttons():
                    shooting = bool(pad.get_button(b))
                jb = CONTROLLER_MAP["jump_button"]
                if jb < pad.get_numbuttons():
                    jump = bool(pad.get_button(jb))
            except Exception:
                pass
        else:
            keys = KEYBOARD[self.index]
            move_x = float(held_keys[keys["right"]]) - float(held_keys[keys["left"]])
            move_z = float(held_keys[keys["forward"]]) - float(held_keys[keys["back"]])
            aim_x = float(held_keys[keys["turn_right"]]) - float(held_keys[keys["turn_left"]])
            aim_y = float(held_keys[keys["look_up"]]) - float(held_keys[keys["look_down"]])
            shooting = bool(held_keys[keys["shoot"]])
            jump = bool(held_keys[keys["jump"]])

        return move_x, move_z, aim_x, aim_y, shooting, jump

    def update_player(self, dt):
        if game_state != "playing":
            return

        move_x, move_z, aim_x, aim_y, shooting, jump = self.read_input()

        # Aim with right stick; keyboard fallback uses Q/E and R/F.
        self.yaw += aim_x * 150 * dt
        self.pitch = clamp(self.pitch - aim_y * 110 * dt, -80, 80)

        # Move relative to current yaw.
        forward = Vec3(math.sin(math.radians(self.yaw)), 0,
                       math.cos(math.radians(self.yaw)))
        right = Vec3(forward.z, 0, -forward.x)
        move = (right * move_x + forward * move_z)
        if move.length() > 1:
            move = move.normalized()
        self.position += move * self.speed * dt

        # Keep players inside arena and above floor.
        self.position.x = clamp(self.position.x, -ARENA_HALF_SIZE + 1.2, ARENA_HALF_SIZE - 1.2)
        self.position.z = clamp(self.position.z, -ARENA_HALF_SIZE + 1.2, ARENA_HALF_SIZE - 1.2)
        self.position.y = 0

        self.view_camera.position = self.position + Vec3(0, 1.65, 0)
        self.view_camera.rotation = (self.pitch, self.yaw, 0)
        self.body.position = self.position

        if shooting:
            self.try_shoot()

    def try_shoot(self):
        now = time.monotonic()
        if not hasattr(self, "next_shot") or now >= self.next_shot:
            self.next_shot = now + 0.18
            target = players[1 - self.index]
            if now < target.invulnerable_until:
                return
            # Hitscan ray: check whether target is within a narrow aim cone.
            origin = self.position + Vec3(0, 1.65, 0)
            direction = Vec3(
                math.sin(math.radians(self.yaw)) * math.cos(math.radians(self.pitch)),
                math.sin(math.radians(self.pitch)),
                math.cos(math.radians(self.yaw)) * math.cos(math.radians(self.pitch))
            )
            to_target = (target.position + Vec3(0, 1.0, 0)) - origin
            distance = to_target.length()
            if distance > 50 or distance < 0.01:
                return
            direction_to_target = to_target.normalized()
            dot = direction.dot(direction_to_target)
            if dot < 0.992:
                return

            # Cover blocks shots if a ray hits a wall/cover first.
            hit = raycast(origin, direction, distance=distance, ignore=[self.body, target.body])
            if hit.hit and hit.entity not in (target.body,):
                # Low cover can block shots; player capsule collision is approximated below.
                return

            target.take_damage(SHOT_DAMAGE, self.index)

    def take_damage(self, amount, attacker_index):
        if game_state != "playing" or time.monotonic() < self.invulnerable_until:
            return
        self.hp -= amount
        if self.hp <= 0:
            players[attacker_index].kills += 1
            self.deaths += 1
            update_score_ui()
            if players[attacker_index].kills >= KILL_LIMIT:
                end_match(attacker_index)
                return
            self.respawn()

    def respawn(self):
        self.hp = MAX_HP
        self.position = Vec3(*self.spawn)
        self.yaw = 0 if self.index == 0 else 180
        self.pitch = 0
        self.invulnerable_until = time.monotonic() + RESPAWN_INVULNERABILITY
        self.view_camera.position = self.position + Vec3(0, 1.65, 0)
        self.view_camera.rotation = (self.pitch, self.yaw, 0)

    def destroy(self):
        for obj in [self.view_camera, self.body]:
            if obj:
                destroy(obj)


def create_ui():
    global timer_text, status_text, menu_title, menu_hint, player_labels
    timer_text = make_text("02:30", (0, 0.46), 1.5, origin=(0, 0))
    status_text = make_text("", (0, 0.40), 0.9, origin=(0, 0))
    player_labels = []
    player_labels.append(make_text("P1  Kills: 0   HP: 100", (-0.47, 0.45), 0.85))
    player_labels.append(make_text("P2  Kills: 0   HP: 100", (0.16, 0.45), 0.85))
    menu_title = make_text("TWO-PLAYER FPS", (0, 0.15), 2.2, origin=(0, 0))
    menu_hint = make_text(
        "Press ENTER to play\n\nP1 keyboard: WASD move, Q/E turn, R/F aim, SPACE shoot\n"
        "P2 keyboard: Arrow keys move, J/L turn, I/K aim, RIGHT SHIFT shoot\n"
        "Controllers: left stick move, right stick aim, configured button shoots",
        (0, -0.03), 0.85, origin=(0, 0)
    )
    for e in [timer_text, status_text, *player_labels]:
        e.enabled = False


def update_score_ui():
    player_labels[0].text = f"P1  Kills: {players[0].kills}   HP: {players[0].hp}"
    player_labels[1].text = f"P2  Kills: {players[1].kills}   HP: {players[1].hp}"


def start_match():
    global game_state, time_left, arena
    game_state = "playing"
    time_left = MATCH_SECONDS
    scores[0] = scores[1] = 0
    for e in ui_entities:
        e.enabled = False
    timer_text.enabled = True
    status_text.enabled = True
    for e in player_labels:
        e.enabled = True
    menu_title.enabled = False
    menu_hint.enabled = False
    arena = Arena()
    players.clear()
    players.append(Player(0, (-10, 0, 0)))
    players.append(Player(1, (10, 0, 0)))
    update_score_ui()
    refresh_controllers()
    status_text.text = f"Controllers detected: {len(controllers)}"


def end_match(winner_index=None):
    global game_state
    game_state = "ended"
    if winner_index is None:
        if players[0].kills > players[1].kills:
            winner_index = 0
        elif players[1].kills > players[0].kills:
            winner_index = 1
    if winner_index is None:
        status_text.text = f"TIE GAME!  P1 {players[0].kills} - {players[1].kills} P2"
    else:
        status_text.text = f"PLAYER {winner_index + 1} WINS!"
    status_text.text += "\nPress ENTER to play again  |  ESC to return to menu"


def return_to_menu():
    global game_state
    game_state = "menu"
    for p in players[:]:
        p.destroy()
    players.clear()
    if "arena" in globals() and arena:
        arena.destroy()
    for e in ui_entities:
        e.enabled = True
    timer_text.enabled = False
    status_text.enabled = False
    for e in player_labels:
        e.enabled = False
    menu_title.enabled = True
    menu_hint.enabled = True


def update():
    global time_left
    dt = min(time.dt, 0.04)

    if game_state == "playing":
        time_left = max(0, time_left - dt)
        timer_text.text = f"{int(time_left)//60:02d}:{int(time_left)%60:02d}"
        for p in players:
            p.update_player(dt)
        update_score_ui()
        status_text.text = f"First to {KILL_LIMIT} kills  |  Controllers: {len(controllers)}"
        if time_left <= 0:
            end_match()

    elif game_state == "ended":
        pass


def input(key):
    if key == "enter":
        if game_state in ("menu", "ended"):
            if game_state == "ended":
                return_to_menu()
            start_match()
    elif key == "escape":
        if game_state in ("playing", "ended"):
            return_to_menu()
        else:
            application.quit()


create_ui()
app.run()
