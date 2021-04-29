// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.ffmpeg.avformat;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;
import org.bytedeco.ffmpeg.avutil.*;
import static org.bytedeco.ffmpeg.global.avutil.*;
import org.bytedeco.ffmpeg.swresample.*;
import static org.bytedeco.ffmpeg.global.swresample.*;
import org.bytedeco.ffmpeg.avcodec.*;
import static org.bytedeco.ffmpeg.global.avcodec.*;

import static org.bytedeco.ffmpeg.global.avformat.*;


/**
 * This structure contains the data a format has to probe a file.
 */
@Properties(inherit = org.bytedeco.ffmpeg.presets.avformat.class)
public class AVProbeData extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public AVProbeData() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public AVProbeData(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public AVProbeData(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public AVProbeData position(long position) {
        return (AVProbeData)super.position(position);
    }
    @Override public AVProbeData getPointer(long i) {
        return new AVProbeData(this).position(position + i);
    }

    public native @Cast("const char*") BytePointer filename(); public native AVProbeData filename(BytePointer setter);
    /** Buffer must have AVPROBE_PADDING_SIZE of extra allocated bytes filled with zero. */
    public native @Cast("unsigned char*") BytePointer buf(); public native AVProbeData buf(BytePointer setter);
    /** Size of buf except extra allocated bytes */
    public native int buf_size(); public native AVProbeData buf_size(int setter);
    /** mime_type, when known. */
    public native @Cast("const char*") BytePointer mime_type(); public native AVProbeData mime_type(BytePointer setter);
}
