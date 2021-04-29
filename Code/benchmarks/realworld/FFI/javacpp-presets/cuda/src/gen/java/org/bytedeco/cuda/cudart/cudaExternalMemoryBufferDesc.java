// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.cuda.cudart;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.cuda.global.cudart.*;


/**
 * External memory buffer descriptor
 */
@Properties(inherit = org.bytedeco.cuda.presets.cudart.class)
public class cudaExternalMemoryBufferDesc extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public cudaExternalMemoryBufferDesc() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public cudaExternalMemoryBufferDesc(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public cudaExternalMemoryBufferDesc(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public cudaExternalMemoryBufferDesc position(long position) {
        return (cudaExternalMemoryBufferDesc)super.position(position);
    }
    @Override public cudaExternalMemoryBufferDesc getPointer(long i) {
        return new cudaExternalMemoryBufferDesc((Pointer)this).position(position + i);
    }

    /**
     * Offset into the memory object where the buffer's base is
     */
    public native @Cast("unsigned long long") long offset(); public native cudaExternalMemoryBufferDesc offset(long setter);
    /**
     * Size of the buffer
     */
    public native @Cast("unsigned long long") long size(); public native cudaExternalMemoryBufferDesc size(long setter);
    /**
     * Flags reserved for future use. Must be zero.
     */
    public native @Cast("unsigned int") int flags(); public native cudaExternalMemoryBufferDesc flags(int setter);
}
