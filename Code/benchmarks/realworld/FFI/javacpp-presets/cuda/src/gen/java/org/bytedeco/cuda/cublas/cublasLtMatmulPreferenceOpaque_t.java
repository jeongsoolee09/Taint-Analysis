// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.cuda.cublas;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;
import org.bytedeco.cuda.cudart.*;
import static org.bytedeco.cuda.global.cudart.*;

import static org.bytedeco.cuda.global.cublas.*;


/** Semi-opaque descriptor for cublasLtMatmulPreference() operation details
 */
@Properties(inherit = org.bytedeco.cuda.presets.cublas.class)
public class cublasLtMatmulPreferenceOpaque_t extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public cublasLtMatmulPreferenceOpaque_t() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public cublasLtMatmulPreferenceOpaque_t(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public cublasLtMatmulPreferenceOpaque_t(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public cublasLtMatmulPreferenceOpaque_t position(long position) {
        return (cublasLtMatmulPreferenceOpaque_t)super.position(position);
    }
    @Override public cublasLtMatmulPreferenceOpaque_t getPointer(long i) {
        return new cublasLtMatmulPreferenceOpaque_t((Pointer)this).position(position + i);
    }

    public native @Cast("uint64_t") long data(int i); public native cublasLtMatmulPreferenceOpaque_t data(int i, long setter);
    @MemberGetter public native @Cast("uint64_t*") LongPointer data();
}
