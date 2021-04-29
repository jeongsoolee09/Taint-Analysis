// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.systems.macosx;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.systems.global.macosx.*;


/* Signal vector template for Kernel user boundary */
@Properties(inherit = org.bytedeco.systems.presets.macosx.class)
public class __sigaction extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public __sigaction() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public __sigaction(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public __sigaction(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public __sigaction position(long position) {
        return (__sigaction)super.position(position);
    }
    @Override public __sigaction getPointer(long i) {
        return new __sigaction(this).position(position + i);
    }

	public native @ByRef __sigaction_u __sigaction_u(); public native __sigaction __sigaction_u(__sigaction_u setter);  /* signal handler */
	public static class Sa_tramp_Pointer_int_int_siginfo_t_Pointer extends FunctionPointer {
	    static { Loader.load(); }
	    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
	    public    Sa_tramp_Pointer_int_int_siginfo_t_Pointer(Pointer p) { super(p); }
	    protected Sa_tramp_Pointer_int_int_siginfo_t_Pointer() { allocate(); }
	    private native void allocate();
	    public native void call(Pointer arg0, int arg1, int arg2, siginfo_t arg3, Pointer arg4);
	}
	public native Sa_tramp_Pointer_int_int_siginfo_t_Pointer sa_tramp(); public native __sigaction sa_tramp(Sa_tramp_Pointer_int_int_siginfo_t_Pointer setter);
	public native @Cast("sigset_t") int sa_mask(); public native __sigaction sa_mask(int setter);               /* signal mask to apply */
	public native int sa_flags(); public native __sigaction sa_flags(int setter);               /* see signal options below */
}
