// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.arrow;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.arrow.global.arrow.*;


/** \brief An operating system file open in write-only mode. */
@Namespace("arrow::io") @NoOffset @Properties(inherit = org.bytedeco.arrow.presets.arrow.class)
public class FileOutputStream extends OutputStream {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public FileOutputStream(Pointer p) { super(p); }


  /** \brief Open a local file for writing, truncating any existing file
   *  @param path [in] with UTF8 encoding
   *  @param append [in] append to existing file, otherwise truncate to 0 bytes
   *  @return an open FileOutputStream
   * 
   *  When opening a new file, any existing file with the indicated path is
   *  truncated to 0 bytes, deleting any existing data */
  
  ///
  public static native @ByVal FileOutputStreamResult Open(@StdString String path,
                                                          @Cast("bool") boolean append/*=false*/);
  public static native @ByVal FileOutputStreamResult Open(@StdString String path);
  public static native @ByVal FileOutputStreamResult Open(@StdString BytePointer path,
                                                          @Cast("bool") boolean append/*=false*/);
  public static native @ByVal FileOutputStreamResult Open(@StdString BytePointer path);

  /** \brief Open a file descriptor for writing.  The underlying file isn't
   *  truncated.
   *  @param fd [in] file descriptor
   *  @return an open FileOutputStream
   * 
   *  The file descriptor becomes owned by the OutputStream, and will be closed
   *  on Close() or destruction. */
  public static native @ByVal FileOutputStreamResult Open(int fd);

  // OutputStream interface
  public native @ByVal Status Close();
  public native @Cast("bool") boolean closed();
  public native @ByVal LongResult Tell();

  // Write bytes to the stream. Thread-safe
  public native @ByVal Status Write(@Const Pointer data, @Cast("int64_t") long nbytes);
  /** \cond FALSE */
  /** \endcond */

  public native int file_descriptor();
}