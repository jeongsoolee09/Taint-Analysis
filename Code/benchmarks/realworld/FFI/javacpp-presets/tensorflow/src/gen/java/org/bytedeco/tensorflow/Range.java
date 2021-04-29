// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.tensorflow;

import org.bytedeco.tensorflow.Allocator;
import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.tensorflow.global.tensorflow.*;


/** Creates a sequence of numbers.
 * 
 *  This operation creates a sequence of numbers that begins at {@code start} and
 *  extends by increments of {@code delta} up to but not including {@code limit}.
 * 
 *  For example:
 * 
 *  <pre>{@code
 *  # 'start' is 3
 *  # 'limit' is 18
 *  # 'delta' is 3
 *  tf.range(start, limit, delta) ==> [3, 6, 9, 12, 15]
 *  }</pre>
 * 
 *  Arguments:
 *  * scope: A Scope object
 *  * start: 0-D (scalar). First entry in the sequence.
 *  * limit: 0-D (scalar). Upper limit of sequence, exclusive.
 *  * delta: 0-D (scalar). Optional. Default is 1. Number that increments {@code start}.
 * 
 *  Returns:
 *  * {@code Output}: 1-D. */
@Namespace("tensorflow::ops") @NoOffset @Properties(inherit = org.bytedeco.tensorflow.presets.tensorflow.class)
public class Range extends Pointer {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public Range(Pointer p) { super(p); }

  public Range(@Const @ByRef Scope scope, @ByVal Input start,
        @ByVal Input _limit, @ByVal Input delta) { super((Pointer)null); allocate(scope, start, _limit, delta); }
  private native void allocate(@Const @ByRef Scope scope, @ByVal Input start,
        @ByVal Input _limit, @ByVal Input delta);
  public native @ByVal @Name("operator tensorflow::Output") Output asOutput();
  public native @ByVal @Name("operator tensorflow::Input") Input asInput();
  public native Node node();

  public native @ByRef Operation operation(); public native Range operation(Operation setter);
  public native @ByRef Output output(); public native Range output(Output setter);
}
