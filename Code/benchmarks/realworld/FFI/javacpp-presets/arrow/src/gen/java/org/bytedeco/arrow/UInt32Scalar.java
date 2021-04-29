// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.arrow;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.arrow.global.arrow.*;


@Namespace("arrow") @Properties(inherit = org.bytedeco.arrow.presets.arrow.class)
public class UInt32Scalar extends BaseUInt32Type {
    static { Loader.load(); }

  
  
    public UInt32Scalar(@Cast("arrow::NumericScalar<arrow::UInt32Type>::ValueType") int value) { super((Pointer)null); allocate(value); }
    private native void allocate(@Cast("arrow::NumericScalar<arrow::UInt32Type>::ValueType") int value);
  
    public UInt32Scalar() { super((Pointer)null); allocate(); }
    private native void allocate();
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public UInt32Scalar(Pointer p) { super(p); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public UInt32Scalar(long size) { super((Pointer)null); allocateArray(size); }
    private native void allocateArray(long size);
    @Override public UInt32Scalar position(long position) {
        return (UInt32Scalar)super.position(position);
    }
    @Override public UInt32Scalar getPointer(long i) {
        return new UInt32Scalar((Pointer)this).position(position + i);
    }

}