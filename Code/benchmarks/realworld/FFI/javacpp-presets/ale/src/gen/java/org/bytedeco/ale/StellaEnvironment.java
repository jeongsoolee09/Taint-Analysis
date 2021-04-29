// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.ale;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.ale.global.ale.*;


@NoOffset @Properties(inherit = org.bytedeco.ale.presets.ale.class)
public class StellaEnvironment extends Pointer {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public StellaEnvironment(Pointer p) { super(p); }

    public StellaEnvironment(OSystem system, RomSettings settings) { super((Pointer)null); allocate(system, settings); }
    private native void allocate(OSystem system, RomSettings settings);

    /** Resets the system to its start state. */
    public native void reset();

    /** Save/restore the environment state onto the stack. */
    public native void save();
    public native void load();

    /** Returns a copy of the current emulator state. Note that this doesn't include
        pseudorandomness, so that clone/restoreState are suitable for planning. */
    public native @ByVal ALEState cloneState();
    /** Restores a previously saved copy of the state. */
    public native void restoreState(@Const @ByRef ALEState arg0);

    /** Returns a copy of the current emulator state. This includes RNG state information, and
        more generally should lead to exactly reproducibility. */
    public native @ByVal ALEState cloneSystemState();
    /** Restores a previously saved copy of the state, including RNG state information. */
    public native void restoreSystemState(@Const @ByRef ALEState arg0);

    /** Applies the given actions (e.g. updating paddle positions when the paddle is used)
      *  and performs one simulation step in Stella. Returns the resultant reward. When 
      *  frame skip is set to > 1, up the corresponding number of simulation steps are performed.
      *  Note that the post-act() frame number might not correspond to the pre-act() frame
      *  number plus the frame skip.
      */
    public native @Cast("reward_t") int act(@Cast("Action") int player_a_action, @Cast("Action") int player_b_action);

    /** This functions emulates a push on the reset button of the console */
    public native void softReset();

    /** Keep pressing the console select button for a given amount of time*/
    public native void pressSelect(@Cast("size_t") long num_steps/*=1*/);
    public native void pressSelect();

    /** Set the difficulty according to the value.
      * If the first bit is 1, then it will put the left difficulty switch to A (otherwise leave it on B)
      * If the second bit is 1, then it will put the right difficulty switch to A (otherwise leave it on B)
      *
      * This change takes effect at the immediate next time step.
      */
    public native void setDifficulty(@Cast("difficulty_t") int value);

    /** Set the game mode according to the value. The new mode will not take effect until reset() is
      * called */
    public native void setMode(@Cast("game_mode_t") int value);

    /** Returns true once we reach a terminal state */
    public native @Cast("bool") boolean isTerminal();

    /** Accessor methods for the environment state. */
    public native void setState(@Const @ByRef ALEState state);
    public native @Const @ByRef ALEState getState();

    /** Returns the current screen after processing (e.g. colour averaging) */
    public native @Const @ByRef ALEScreen getScreen();
    public native @Const @ByRef ALERAM getRAM();

    public native int getFrameNumber();
    public native int getEpisodeFrameNumber();

    /** Returns a wrapper providing #include-free access to our methods. */ 
    public native @Name("getWrapper().get") StellaEnvironmentWrapper getWrapper();
}