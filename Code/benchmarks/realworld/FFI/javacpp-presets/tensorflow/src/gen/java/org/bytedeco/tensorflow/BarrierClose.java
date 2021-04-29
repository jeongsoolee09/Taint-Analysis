// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.tensorflow;

import org.bytedeco.tensorflow.Allocator;
import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.tensorflow.global.tensorflow.*;


/** Closes the given barrier.
 * 
 *  This operation signals that no more new elements will be inserted in the
 *  given barrier. Subsequent InsertMany that try to introduce a new key will fail.
 *  Subsequent InsertMany operations that just add missing components to already
 *  existing elements will continue to succeed. Subsequent TakeMany operations will
 *  continue to succeed if sufficient completed elements remain in the barrier.
 *  Subsequent TakeMany operations that would block will fail immediately.
 * 
 *  Arguments:
 *  * scope: A Scope object
 *  * handle: The handle to a barrier.
 * 
 *  Optional attributes (see {@code Attrs}):
 *  * cancel_pending_enqueues: If true, all pending enqueue requests that are
 *  blocked on the barrier's queue will be canceled. InsertMany will fail, even
 *  if no new key is introduced.
 * 
 *  Returns:
 *  * the created {@code Operation} */
@Namespace("tensorflow::ops") @NoOffset @Properties(inherit = org.bytedeco.tensorflow.presets.tensorflow.class)
public class BarrierClose extends Pointer {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public BarrierClose(Pointer p) { super(p); }

  /** Optional attribute setters for BarrierClose */
  public static class Attrs extends Pointer {
      static { Loader.load(); }
      /** Default native constructor. */
      public Attrs() { super((Pointer)null); allocate(); }
      /** Native array allocator. Access with {@link Pointer#position(long)}. */
      public Attrs(long size) { super((Pointer)null); allocateArray(size); }
      /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
      public Attrs(Pointer p) { super(p); }
      private native void allocate();
      private native void allocateArray(long size);
      @Override public Attrs position(long position) {
          return (Attrs)super.position(position);
      }
      @Override public Attrs getPointer(long i) {
          return new Attrs(this).position(position + i);
      }
  
    /** If true, all pending enqueue requests that are
     *  blocked on the barrier's queue will be canceled. InsertMany will fail, even
     *  if no new key is introduced.
     * 
     *  Defaults to false */
    public native @ByVal Attrs CancelPendingEnqueues(@Cast("bool") boolean x);

    public native @Cast("bool") boolean cancel_pending_enqueues_(); public native Attrs cancel_pending_enqueues_(boolean setter);
  }
  public BarrierClose(@Const @ByRef Scope scope, @ByVal Input handle) { super((Pointer)null); allocate(scope, handle); }
  private native void allocate(@Const @ByRef Scope scope, @ByVal Input handle);
  public BarrierClose(@Const @ByRef Scope scope, @ByVal Input handle,
               @Const @ByRef Attrs attrs) { super((Pointer)null); allocate(scope, handle, attrs); }
  private native void allocate(@Const @ByRef Scope scope, @ByVal Input handle,
               @Const @ByRef Attrs attrs);
  public native @ByVal @Name("operator tensorflow::Operation") Operation asOperation();

  public static native @ByVal Attrs CancelPendingEnqueues(@Cast("bool") boolean x);

  public native @ByRef Operation operation(); public native BarrierClose operation(Operation setter);
}
