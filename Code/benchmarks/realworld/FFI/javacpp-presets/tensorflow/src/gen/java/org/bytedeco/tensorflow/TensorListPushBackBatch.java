// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.tensorflow;

import org.bytedeco.tensorflow.Allocator;
import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.tensorflow.global.tensorflow.*;


/** TODO: add doc.
 * 
 *  Arguments:
 *  * scope: A Scope object
 * 
 *  Returns:
 *  * {@code Output}: The output_handles tensor. */
@Namespace("tensorflow::ops") @NoOffset @Properties(inherit = org.bytedeco.tensorflow.presets.tensorflow.class)
public class TensorListPushBackBatch extends Pointer {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public TensorListPushBackBatch(Pointer p) { super(p); }

  public TensorListPushBackBatch(@Const @ByRef Scope scope, @ByVal Input input_handles, @ByVal Input tensor) { super((Pointer)null); allocate(scope, input_handles, tensor); }
  private native void allocate(@Const @ByRef Scope scope, @ByVal Input input_handles, @ByVal Input tensor);
  public native @ByVal @Name("operator tensorflow::Output") Output asOutput();
  public native @ByVal @Name("operator tensorflow::Input") Input asInput();
  public native Node node();

  public native @ByRef Operation operation(); public native TensorListPushBackBatch operation(Operation setter);
  public native @ByRef Output output_handles(); public native TensorListPushBackBatch output_handles(Output setter);
}