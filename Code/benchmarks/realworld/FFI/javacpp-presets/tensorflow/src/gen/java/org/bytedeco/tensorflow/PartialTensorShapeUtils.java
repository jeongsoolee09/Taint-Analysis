// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.tensorflow;

import org.bytedeco.tensorflow.Allocator;
import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.tensorflow.global.tensorflow.*;


/** \brief Static helper routines for {@code PartialTensorShape}. Includes a few
 *  common predicates on a partially known tensor shape. */
@Namespace("tensorflow") @Properties(inherit = org.bytedeco.tensorflow.presets.tensorflow.class)
public class PartialTensorShapeUtils extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public PartialTensorShapeUtils() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public PartialTensorShapeUtils(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public PartialTensorShapeUtils(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public PartialTensorShapeUtils position(long position) {
        return (PartialTensorShapeUtils)super.position(position);
    }
    @Override public PartialTensorShapeUtils getPointer(long i) {
        return new PartialTensorShapeUtils(this).position(position + i);
    }

  public static native @StdString BytePointer PartialShapeListString(
        @ArraySlice PartialTensorShape shapes);

  public static native @Cast("bool") boolean AreIdentical(@ArraySlice PartialTensorShape shapes0,
                             @ArraySlice PartialTensorShape shapes1);

  public static native @Cast("bool") boolean AreCompatible(@ArraySlice PartialTensorShape shapes0,
                              @ArraySlice PartialTensorShape shapes1);
}
