
from enum import Enum
from manim import * 

class Direction(Enum):
    LEFT = 'L'
    RIGHT = 'R'

class TM: 
    def __init__(
            self, 
            delta: dict, 
            tape: list, 
            initial_state: str = 'q0',
            final_states: set | None = None
        ): 
        if final_states is None:
            final_states = set(['HALT'])
        self.delta = delta 
        self.tape = tape.copy()
        self.head_pos = 0 
        self.state = initial_state
        self.final_states = final_states
        self.initial_state = initial_state
        self.initial_tape = tape.copy()  # Store initial tape for reset
        self.extended_left = 0
        self.extended_right = 0
        print("Initial Tape: ", ''.join(self.tape))
        print("Initial State: ", self.state)
        print("Final States: ", self.final_states)
    
    def reset(self):
        self.head_pos = self.extended_left  # Reset head position to the start of the initial tape
        self.state = self.initial_state
        self.tape = [' '] * self.extended_left + self.initial_tape + [' '] * self.extended_right
        self.extended_left = 0
        self.extended_right = 0

    def step(self, callbacks = None): 
        if self.state in self.final_states:
            return 
        if callbacks is None:
            callbacks = {}
        current_symbol = self.tape[self.head_pos] 
        if self.state not in self.delta:
            raise RuntimeError(f"State {self.state} not in transition function.")
        if current_symbol not in self.delta[self.state]:
            raise RuntimeError(f"Symbol {current_symbol} not in transition function for state {self.state}.")
        new_state, new_symbol, direction = self.delta[self.state][current_symbol]
        self.tape[self.head_pos] = new_symbol
        self.state = new_state
        if direction == Direction.RIGHT:
            self.head_pos += 1
            if self.head_pos == len(self.tape):
                self.tape.append(' ')  # Extend tape with blank symbol
                self.extended_right += 1
                callbacks.get('extend_right', lambda: None)() 
        elif direction == Direction.LEFT:
            self.head_pos -= 1
            if self.head_pos < 0:
                self.tape.insert(0, ' ')  # Extend tape with blank symbol
                self.head_pos = 0
                self.extended_left += 1
                callbacks.get('extend_left', lambda: None)()  # Call callback if provided
        else:
            raise RuntimeError(f"Invalid direction {direction} in transition function.")
    def run(self, scene: Scene | None = None, max_steps: int = 1000): 
        if scene is None:
            for _ in range(max_steps):
                self.step()
                if self.state in self.final_states:
                    break
            print("Final Tape: ", ''.join(self.tape))
            return 
        # First, figure out number of tape cells needed for visualization
        self.run(max_steps=max_steps)
        tape_cell_count = len(self.tape)
        self.reset()  # Reset to initial state for visualization
        # visualization code using manim
        tape_cells = VGroup(*[Square(side_length=0.5) for _ in range(tape_cell_count)]).arrange(RIGHT, buff=0)
        cell_texts = VGroup(*[Text(self.tape[i], font_size=24).move_to(tape_cells[i].get_center()) for i in range(tape_cell_count)])
        tape_cells.set_color(WHITE)
        head_indicator = Arrow(UP, DOWN, color=RED)
        head_indicator.next_to(tape_cells[self.head_pos], UP)
        state_text = Text(self.state).to_edge(UP)
        scene.add(tape_cells, head_indicator, state_text, cell_texts)
        
        scene.play(*[cell.animate.set_fill(GRAY if i == self.head_pos else BLACK, opacity=1) for i, cell in enumerate(tape_cells)])
        for _ in range(max_steps):
            old_pos = self.head_pos
            self.step()
            new_text = Text(
                        self.tape[old_pos], 
                        font_size=24
                    ).move_to(tape_cells[old_pos].get_center())
            scene.play(
                ReplacementTransform(cell_texts[old_pos],
                    new_text
                )
            )
            new_state_text = Text(self.state).to_edge(UP)
            # Update visualization
            scene.play(
                head_indicator.animate.next_to(tape_cells[self.head_pos], UP),
                *[cell.animate.set_fill(GRAY if i == self.head_pos else BLACK, opacity=1) for i, cell in enumerate(tape_cells)],
                ReplacementTransform(state_text, new_state_text)
            )
            state_text = new_state_text
            cell_texts[old_pos] = new_text
            if self.state in self.final_states:
                break

class TMSimulation(Scene):
    def construct(self):
        delta = {
            'q0': {
                '0': ('q0', '1', Direction.RIGHT), 
                '1': ('q0', '0', Direction.RIGHT), 
                ' ': ('q1', ' ', Direction.LEFT)
            },
            'q1': {
                '0': ('q1', '1', Direction.LEFT), 
                '1': ('q1', '0', Direction.LEFT), 
                ' ': ('HALT', ' ', Direction.RIGHT)
            }
        }
        tape = ['0'] *3  # Initial tape with 10 blank symbols
        tm = TM(delta, tape)
        tm.run(self, max_steps=10)