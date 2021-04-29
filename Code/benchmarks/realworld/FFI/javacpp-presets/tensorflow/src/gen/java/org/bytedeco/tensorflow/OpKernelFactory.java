// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.tensorflow;

import org.bytedeco.tensorflow.Allocator;
import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.tensorflow.global.tensorflow.*;


// OpKernelFactory is responsible for creating OpKernels when TensorFlow needs
// them. You register factories with the TensorFlow core by constructing an
// OpKernelRegistrar and passing the factory as a constructor parameter.
@Namespace("tensorflow::kernel_factory") @Properties(inherit = org.bytedeco.tensorflow.presets.tensorflow.class)
public class OpKernelFactory extends Pointer {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public OpKernelFactory(Pointer p) { super(p); }

  public native OpKernel Create(OpKernelConstruction context);
}
