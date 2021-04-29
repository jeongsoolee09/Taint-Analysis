// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.tesseract;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;
import org.bytedeco.leptonica.*;
import static org.bytedeco.leptonica.global.lept.*;

import static org.bytedeco.tesseract.global.tesseract.*;


// Simple file class.
// Allows for portable file input from memory and from foreign file systems.
@Namespace("tesseract") @NoOffset @Properties(inherit = org.bytedeco.tesseract.presets.tesseract.class)
public class TFile extends Pointer {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public TFile(Pointer p) { super(p); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public TFile(long size) { super((Pointer)null); allocateArray(size); }
    private native void allocateArray(long size);
    @Override public TFile position(long position) {
        return (TFile)super.position(position);
    }
    @Override public TFile getPointer(long i) {
        return new TFile(this).position(position + i);
    }

  public TFile() { super((Pointer)null); allocate(); }
  private native void allocate();

  // All the Open methods load the whole file into memory for reading.
  // Opens a file with a supplied reader, or nullptr to use the default.
  // Note that mixed read/write is not supported.
  public native @Cast("bool") boolean Open(@Const @ByRef STRING filename, FileReader reader);
  // From an existing memory buffer.
  public native @Cast("bool") boolean Open(@Cast("const char*") BytePointer data, int size);
  public native @Cast("bool") boolean Open(String data, int size);
  // From an open file and an end offset.
  public native @Cast("bool") boolean Open(@Cast("FILE*") Pointer fp, @Cast("int64_t") long end_offset);
  // Sets the value of the swap flag, so that FReadEndian does the right thing.
  public native void set_swap(@Cast("bool") boolean value);

  // Deserialize data.
  public native @Cast("bool") boolean DeSerialize(@Cast("char*") BytePointer data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean DeSerialize(@Cast("char*") BytePointer data);
  public native @Cast("bool") boolean DeSerialize(@Cast("char*") ByteBuffer data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean DeSerialize(@Cast("char*") ByteBuffer data);
  public native @Cast("bool") boolean DeSerialize(@Cast("char*") byte[] data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean DeSerialize(@Cast("char*") byte[] data);
  public native @Cast("bool") boolean DeSerialize(DoublePointer data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean DeSerialize(DoublePointer data);
  public native @Cast("bool") boolean DeSerialize(DoubleBuffer data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean DeSerialize(DoubleBuffer data);
  public native @Cast("bool") boolean DeSerialize(double[] data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean DeSerialize(double[] data);
  public native @Cast("bool") boolean DeSerialize(FloatPointer data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean DeSerialize(FloatPointer data);
  public native @Cast("bool") boolean DeSerialize(FloatBuffer data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean DeSerialize(FloatBuffer data);
  public native @Cast("bool") boolean DeSerialize(float[] data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean DeSerialize(float[] data);
  public native @Cast("bool") boolean DeSerialize(ShortPointer data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean DeSerialize(ShortPointer data);
  public native @Cast("bool") boolean DeSerialize(ShortBuffer data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean DeSerialize(ShortBuffer data);
  public native @Cast("bool") boolean DeSerialize(short[] data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean DeSerialize(short[] data);
  public native @Cast("bool") boolean DeSerialize(IntPointer data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean DeSerialize(IntPointer data);
  public native @Cast("bool") boolean DeSerialize(IntBuffer data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean DeSerialize(IntBuffer data);
  public native @Cast("bool") boolean DeSerialize(int[] data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean DeSerialize(int[] data);
  public native @Cast("bool") boolean DeSerialize(@Cast("int64_t*") LongPointer data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean DeSerialize(@Cast("int64_t*") LongPointer data);
  public native @Cast("bool") boolean DeSerialize(@Cast("int64_t*") LongBuffer data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean DeSerialize(@Cast("int64_t*") LongBuffer data);
  public native @Cast("bool") boolean DeSerialize(@Cast("int64_t*") long[] data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean DeSerialize(@Cast("int64_t*") long[] data);

  // Serialize data.
  public native @Cast("bool") boolean Serialize(@Cast("const char*") BytePointer data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean Serialize(@Cast("const char*") BytePointer data);
  public native @Cast("bool") boolean Serialize(String data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean Serialize(String data);
  public native @Cast("bool") boolean Serialize(@Const DoublePointer data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean Serialize(@Const DoublePointer data);
  public native @Cast("bool") boolean Serialize(@Const DoubleBuffer data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean Serialize(@Const DoubleBuffer data);
  public native @Cast("bool") boolean Serialize(@Const double[] data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean Serialize(@Const double[] data);
  public native @Cast("bool") boolean Serialize(@Const FloatPointer data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean Serialize(@Const FloatPointer data);
  public native @Cast("bool") boolean Serialize(@Const FloatBuffer data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean Serialize(@Const FloatBuffer data);
  public native @Cast("bool") boolean Serialize(@Const float[] data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean Serialize(@Const float[] data);
  public native @Cast("bool") boolean Serialize(@Const ByteBuffer data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean Serialize(@Const ByteBuffer data);
  public native @Cast("bool") boolean Serialize(@Const byte[] data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean Serialize(@Const byte[] data);
  public native @Cast("bool") boolean Serialize(@Const ShortPointer data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean Serialize(@Const ShortPointer data);
  public native @Cast("bool") boolean Serialize(@Const ShortBuffer data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean Serialize(@Const ShortBuffer data);
  public native @Cast("bool") boolean Serialize(@Const short[] data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean Serialize(@Const short[] data);
  public native @Cast("bool") boolean Serialize(@Const IntPointer data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean Serialize(@Const IntPointer data);
  public native @Cast("bool") boolean Serialize(@Const IntBuffer data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean Serialize(@Const IntBuffer data);
  public native @Cast("bool") boolean Serialize(@Const int[] data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean Serialize(@Const int[] data);
  public native @Cast("bool") boolean Serialize(@Cast("const int64_t*") LongPointer data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean Serialize(@Cast("const int64_t*") LongPointer data);
  public native @Cast("bool") boolean Serialize(@Cast("const int64_t*") LongBuffer data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean Serialize(@Cast("const int64_t*") LongBuffer data);
  public native @Cast("bool") boolean Serialize(@Cast("const int64_t*") long[] data, @Cast("size_t") long count/*=1*/);
  public native @Cast("bool") boolean Serialize(@Cast("const int64_t*") long[] data);

  // Skip data.
  public native @Cast("bool") boolean Skip(@Cast("size_t") long count);

  // Reads a line like fgets. Returns nullptr on EOF, otherwise buffer.
  // Reads at most buffer_size bytes, including '\0' terminator, even if
  // the line is longer. Does nothing if buffer_size <= 0.
  public native @Cast("char*") BytePointer FGets(@Cast("char*") BytePointer buffer, int buffer_size);
  public native @Cast("char*") ByteBuffer FGets(@Cast("char*") ByteBuffer buffer, int buffer_size);
  public native @Cast("char*") byte[] FGets(@Cast("char*") byte[] buffer, int buffer_size);
  // Replicates fread, followed by a swap of the bytes if needed, returning the
  // number of items read. If swap_ is true then the count items will each have
  // size bytes reversed.
  public native int FReadEndian(Pointer buffer, @Cast("size_t") long size, int count);
  // Replicates fread, returning the number of items read.
  public native int FRead(Pointer buffer, @Cast("size_t") long size, int count);
  // Resets the TFile as if it has been Opened, but nothing read.
  // Only allowed while reading!
  public native void Rewind();

  // Open for writing. Either supply a non-nullptr data with OpenWrite before
  // calling FWrite, (no close required), or supply a nullptr data to OpenWrite
  // and call CloseWrite to write to a file after the FWrites.
  public native void OpenWrite(CharGenericVector data);
  public native @Cast("bool") boolean CloseWrite(@Const @ByRef STRING filename, FileWriter writer);

  // Replicates fwrite, returning the number of items written.
  // To use fprintf, use snprintf and FWrite.
  public native int FWrite(@Const Pointer buffer, @Cast("size_t") long size, int count);
}
