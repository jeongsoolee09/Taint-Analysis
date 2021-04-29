// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.systems.linux;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.systems.global.linux.*;

// #endif


/* Structure describing a signal stack (obsolete).  */
@Name("struct sigstack") @Properties(inherit = org.bytedeco.systems.presets.linux.class)
public class sigstack extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public sigstack() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public sigstack(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public sigstack(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public sigstack position(long position) {
        return (sigstack)super.position(position);
    }
    @Override public sigstack getPointer(long i) {
        return new sigstack(this).position(position + i);
    }

    public native Pointer ss_sp(); public native sigstack ss_sp(Pointer setter);		/* Signal stack pointer.  */
    public native int ss_onstack(); public native sigstack ss_onstack(int setter);		/* Nonzero if executing on this stack.  */
  }
