// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.arrow;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.arrow.global.arrow.*;


/** \brief Concrete type class for variable-size string data, utf8-encoded */
@Namespace("arrow") @NoOffset @Properties(inherit = org.bytedeco.arrow.presets.arrow.class)
public class StringType extends BinaryType {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public StringType(Pointer p) { super(p); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public StringType(long size) { super((Pointer)null); allocateArray(size); }
    private native void allocateArray(long size);
    @Override public StringType position(long position) {
        return (StringType)super.position(position);
    }
    @Override public StringType getPointer(long i) {
        return new StringType((Pointer)this).position(position + i);
    }

  @MemberGetter public static native @Cast("const arrow::Type::type") int type_id();
  public static final int type_id = type_id();
  @MemberGetter public static native @Cast("const bool") boolean is_utf8();
  public static final boolean is_utf8 = is_utf8();

  public static native String type_name();

  public StringType() { super((Pointer)null); allocate(); }
  private native void allocate();

  public native @StdString String ToString();
  public native @StdString String name();
}
