// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.tensorflow;

import org.bytedeco.tensorflow.Allocator;
import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.tensorflow.global.tensorflow.*;


/** Represents a thread used to run a Tensorflow function. */
@Namespace("tensorflow") @Properties(inherit = org.bytedeco.tensorflow.presets.tensorflow.class)
public class Thread extends Pointer {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public Thread(Pointer p) { super(p); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public Thread(long size) { super((Pointer)null); allocateArray(size); }
    private native void allocateArray(long size);
    @Override public Thread position(long position) {
        return (Thread)super.position(position);
    }
    @Override public Thread getPointer(long i) {
        return new Thread(this).position(position + i);
    }

  public Thread() { super((Pointer)null); allocate(); }
  private native void allocate();

  /** Blocks until the thread of control stops running. */
}
