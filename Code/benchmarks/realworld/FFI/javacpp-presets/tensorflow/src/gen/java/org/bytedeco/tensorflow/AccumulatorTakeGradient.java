// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.tensorflow;

import org.bytedeco.tensorflow.Allocator;
import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.tensorflow.global.tensorflow.*;


/** Extracts the average gradient in the given ConditionalAccumulator.
 * 
 *  The op blocks until sufficient (i.e., more than num_required)
 *  gradients have been accumulated.  If the accumulator has already
 *  aggregated more than num_required gradients, it returns the average of
 *  the accumulated gradients.  Also automatically increments the recorded
 *  global_step in the accumulator by 1, and resets the aggregate to 0.
 * 
 *  Arguments:
 *  * scope: A Scope object
 *  * handle: The handle to an accumulator.
 *  * num_required: Number of gradients required before we return an aggregate.
 *  * dtype: The data type of accumulated gradients. Needs to correspond to the type
 *  of the accumulator.
 * 
 *  Returns:
 *  * {@code Output}: The average of the accumulated gradients. */
@Namespace("tensorflow::ops") @NoOffset @Properties(inherit = org.bytedeco.tensorflow.presets.tensorflow.class)
public class AccumulatorTakeGradient extends Pointer {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public AccumulatorTakeGradient(Pointer p) { super(p); }

  public AccumulatorTakeGradient(@Const @ByRef Scope scope, @ByVal Input handle, @ByVal Input num_required, @Cast("tensorflow::DataType") int dtype) { super((Pointer)null); allocate(scope, handle, num_required, dtype); }
  private native void allocate(@Const @ByRef Scope scope, @ByVal Input handle, @ByVal Input num_required, @Cast("tensorflow::DataType") int dtype);
  public native @ByVal @Name("operator tensorflow::Output") Output asOutput();
  public native @ByVal @Name("operator tensorflow::Input") Input asInput();
  public native Node node();

  public native @ByRef Operation operation(); public native AccumulatorTakeGradient operation(Operation setter);
  public native @ByRef Output average(); public native AccumulatorTakeGradient average(Output setter);
}
