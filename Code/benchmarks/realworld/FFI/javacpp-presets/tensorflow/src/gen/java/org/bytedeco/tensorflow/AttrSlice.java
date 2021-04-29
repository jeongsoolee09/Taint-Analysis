// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.tensorflow;

import org.bytedeco.tensorflow.Allocator;
import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.tensorflow.global.tensorflow.*;


@Namespace("tensorflow") @NoOffset @Properties(inherit = org.bytedeco.tensorflow.presets.tensorflow.class)
public class AttrSlice extends Pointer {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public AttrSlice(Pointer p) { super(p); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public AttrSlice(long size) { super((Pointer)null); allocateArray(size); }
    private native void allocateArray(long size);
    @Override public AttrSlice position(long position) {
        return (AttrSlice)super.position(position);
    }
    @Override public AttrSlice getPointer(long i) {
        return new AttrSlice(this).position(position + i);
    }

  public AttrSlice(@Const @ByRef NodeDef node_def) { super((Pointer)null); allocate(node_def); }
  private native void allocate(@Const @ByRef NodeDef node_def);  // NOLINT(runtime/explicit)

  public AttrSlice() { super((Pointer)null); allocate(); }
  private native void allocate();  // Empty
  public AttrSlice(@Cast("const tensorflow::AttrValueMap*") StringAttrValueMap a) { super((Pointer)null); allocate(a); }
  private native void allocate(@Cast("const tensorflow::AttrValueMap*") StringAttrValueMap a);

  public native int size();

  // Returns the attr with attr_name if found.  Otherwise, returns
  // nullptr.
  public native @Const AttrValue Find(@StringPiece BytePointer attr_name);
  public native @Const AttrValue Find(@StringPiece String attr_name);

  // Returns the attr_value for attr_name if found. Otherwise, returns a
  // NotFound status.
  public native @ByVal Status Find(@StringPiece BytePointer attr_name, @Cast("const tensorflow::AttrValue**") PointerPointer attr_value);
  public native @ByVal Status Find(@StringPiece BytePointer attr_name, @Const @ByPtrPtr AttrValue attr_value);
  public native @ByVal Status Find(@StringPiece String attr_name, @Const @ByPtrPtr AttrValue attr_value);

  // Helper class to avoid allocations in EqualAttrs.
  // TODO(irving): Will go away once NodeInfo is used.
  public static class Scratch extends Pointer {
      static { Loader.load(); }
      /** Default native constructor. */
      public Scratch() { super((Pointer)null); allocate(); }
      /** Native array allocator. Access with {@link Pointer#position(long)}. */
      public Scratch(long size) { super((Pointer)null); allocateArray(size); }
      /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
      public Scratch(Pointer p) { super(p); }
      private native void allocate();
      private native void allocateArray(long size);
      @Override public Scratch position(long position) {
          return (Scratch)super.position(position);
      }
      @Override public Scratch getPointer(long i) {
          return new Scratch(this).position(position + i);
      }
  
    public native @StdString BytePointer a(); public native Scratch a(BytePointer setter);
    public native @StdString BytePointer b(); public native Scratch b(BytePointer setter);
  }

  // Check if all attrs and attr values match.  Does not take defaults into
  // account.
  //
  // TODO(irving): There is a bug in this routine inherited from its
  // OptimizerCSE::EqualAttrs precedecessor.  The same tensor attr can be
  // represented in more than one way as an AttrValue, since TensorProto is
  // not 1-1.  This bug will go away once I replace everything with NodeInfo,
  // which stores a Tensor object directly.  The Scratch object will also go
  // away.
  public native @Cast("bool") boolean EqualAttrs(@ByVal AttrSlice other, Scratch scratch);

  // If this AttrSlice has an attached NodeDef, summarize it.  This is for
  // error messages only: we intentionally do not provide direct access to the
  // NodeDef, since it is not always there.
  public native @StdString BytePointer SummarizeNode();

  // Iteration over all attrs

  public native @StdString BytePointer DebugString();
}
