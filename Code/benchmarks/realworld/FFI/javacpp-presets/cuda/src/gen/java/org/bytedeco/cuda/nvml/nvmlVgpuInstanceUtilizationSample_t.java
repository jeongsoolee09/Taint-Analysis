// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.cuda.nvml;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;
import org.bytedeco.cuda.cudart.*;
import static org.bytedeco.cuda.global.cudart.*;

import static org.bytedeco.cuda.global.nvml.*;


/**
 * Structure to store Utilization Value and vgpuInstance
 */
@Properties(inherit = org.bytedeco.cuda.presets.nvml.class)
public class nvmlVgpuInstanceUtilizationSample_t extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public nvmlVgpuInstanceUtilizationSample_t() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public nvmlVgpuInstanceUtilizationSample_t(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public nvmlVgpuInstanceUtilizationSample_t(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public nvmlVgpuInstanceUtilizationSample_t position(long position) {
        return (nvmlVgpuInstanceUtilizationSample_t)super.position(position);
    }
    @Override public nvmlVgpuInstanceUtilizationSample_t getPointer(long i) {
        return new nvmlVgpuInstanceUtilizationSample_t((Pointer)this).position(position + i);
    }

    /** vGPU Instance */
    public native @Cast("nvmlVgpuInstance_t") int vgpuInstance(); public native nvmlVgpuInstanceUtilizationSample_t vgpuInstance(int setter);
    /** CPU Timestamp in microseconds */
    public native @Cast("unsigned long long") long timeStamp(); public native nvmlVgpuInstanceUtilizationSample_t timeStamp(long setter);
    /** SM (3D/Compute) Util Value */
    public native @ByRef nvmlValue_t smUtil(); public native nvmlVgpuInstanceUtilizationSample_t smUtil(nvmlValue_t setter);
    /** Frame Buffer Memory Util Value */
    public native @ByRef nvmlValue_t memUtil(); public native nvmlVgpuInstanceUtilizationSample_t memUtil(nvmlValue_t setter);
    /** Encoder Util Value */
    public native @ByRef nvmlValue_t encUtil(); public native nvmlVgpuInstanceUtilizationSample_t encUtil(nvmlValue_t setter);
    /** Decoder Util Value */
    public native @ByRef nvmlValue_t decUtil(); public native nvmlVgpuInstanceUtilizationSample_t decUtil(nvmlValue_t setter);
}
