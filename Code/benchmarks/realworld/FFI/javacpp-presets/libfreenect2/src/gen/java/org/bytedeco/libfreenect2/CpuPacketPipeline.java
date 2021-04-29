// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.libfreenect2;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.libfreenect2.global.freenect2.*;


/** Pipeline with CPU depth processing. */
@Namespace("libfreenect2") @Properties(inherit = org.bytedeco.libfreenect2.presets.freenect2.class)
public class CpuPacketPipeline extends PacketPipeline {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public CpuPacketPipeline(Pointer p) { super(p); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public CpuPacketPipeline(long size) { super((Pointer)null); allocateArray(size); }
    private native void allocateArray(long size);
    @Override public CpuPacketPipeline position(long position) {
        return (CpuPacketPipeline)super.position(position);
    }
    @Override public CpuPacketPipeline getPointer(long i) {
        return new CpuPacketPipeline(this).position(position + i);
    }

  public CpuPacketPipeline() { super((Pointer)null); allocate(); }
  private native void allocate();
}
