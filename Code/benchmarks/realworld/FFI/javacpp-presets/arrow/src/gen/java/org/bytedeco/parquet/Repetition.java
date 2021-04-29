// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.parquet;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;
import org.bytedeco.arrow.*;
import static org.bytedeco.arrow.global.arrow.*;

import static org.bytedeco.arrow.global.parquet.*;


// Mirrors parquet::FieldRepetitionType
@Namespace("parquet") @Properties(inherit = org.bytedeco.arrow.presets.parquet.class)
public class Repetition extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public Repetition() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public Repetition(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public Repetition(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public Repetition position(long position) {
        return (Repetition)super.position(position);
    }
    @Override public Repetition getPointer(long i) {
        return new Repetition((Pointer)this).position(position + i);
    }

  public enum type { REQUIRED(0), OPTIONAL(1), REPEATED(2), /*Always last*/ UNDEFINED(3);

      public final int value;
      private type(int v) { this.value = v; }
      private type(type e) { this.value = e.value; }
      public type intern() { for (type e : values()) if (e.value == value) return e; return this; }
      @Override public String toString() { return intern().name(); }
  }
}