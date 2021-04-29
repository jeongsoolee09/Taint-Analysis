// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.cuda.cublas;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;
import org.bytedeco.cuda.cudart.*;
import static org.bytedeco.cuda.global.cudart.*;

import static org.bytedeco.cuda.global.cublas.*;


/** Semi-opaque descriptor for cublasLtMatrixTransform() operation details
 */
@Properties(inherit = org.bytedeco.cuda.presets.cublas.class)
public class cublasLtMatrixTransformDescOpaque_t extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public cublasLtMatrixTransformDescOpaque_t() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public cublasLtMatrixTransformDescOpaque_t(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public cublasLtMatrixTransformDescOpaque_t(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public cublasLtMatrixTransformDescOpaque_t position(long position) {
        return (cublasLtMatrixTransformDescOpaque_t)super.position(position);
    }
    @Override public cublasLtMatrixTransformDescOpaque_t getPointer(long i) {
        return new cublasLtMatrixTransformDescOpaque_t((Pointer)this).position(position + i);
    }

    public native @Cast("uint64_t") long data(int i); public native cublasLtMatrixTransformDescOpaque_t data(int i, long setter);
    @MemberGetter public native @Cast("uint64_t*") LongPointer data();
}
