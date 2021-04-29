// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.opencl;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.opencl.global.OpenCL.*;


@Properties(inherit = org.bytedeco.opencl.presets.OpenCL.class)
public class cl_long4 extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public cl_long4() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public cl_long4(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public cl_long4(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public cl_long4 position(long position) {
        return (cl_long4)super.position(position);
    }
    @Override public cl_long4 getPointer(long i) {
        return new cl_long4(this).position(position + i);
    }

    public native @Cast("cl_long") int s(int i); public native cl_long4 s(int i, int setter);
    @MemberGetter public native @Cast("cl_long*") IntPointer s();
// #if __CL_HAS_ANON_STRUCT__
// #endif
// #if defined( __CL_LONG2__)
// #endif
// #if defined( __CL_LONG4__)
// #endif
}
