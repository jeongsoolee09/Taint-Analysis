// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.cuda.cudart;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.cuda.global.cudart.*;


/**
 * Per-operation parameters for ::cuStreamBatchMemOp
 */
@Properties(inherit = org.bytedeco.cuda.presets.cudart.class)
public class CUstreamBatchMemOpParams extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public CUstreamBatchMemOpParams() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public CUstreamBatchMemOpParams(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public CUstreamBatchMemOpParams(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public CUstreamBatchMemOpParams position(long position) {
        return (CUstreamBatchMemOpParams)super.position(position);
    }
    @Override public CUstreamBatchMemOpParams getPointer(long i) {
        return new CUstreamBatchMemOpParams((Pointer)this).position(position + i);
    }

    public native @Cast("CUstreamBatchMemOpType") int operation(); public native CUstreamBatchMemOpParams operation(int setter);
        @Name("waitValue.operation") public native @Cast("CUstreamBatchMemOpType") int waitValue_operation(); public native CUstreamBatchMemOpParams waitValue_operation(int setter);
        @Name("waitValue.address") public native @Cast("CUdeviceptr") long waitValue_address(); public native CUstreamBatchMemOpParams waitValue_address(long setter);
            @Name("waitValue.value") public native @Cast("cuuint32_t") int waitValue_value(); public native CUstreamBatchMemOpParams waitValue_value(int setter);
            @Name("waitValue.value64") public native @Cast("cuuint64_t") int waitValue_value64(); public native CUstreamBatchMemOpParams waitValue_value64(int setter);
        @Name("waitValue.flags") public native @Cast("unsigned int") int waitValue_flags(); public native CUstreamBatchMemOpParams waitValue_flags(int setter);
        /** For driver internal use. Initial value is unimportant. */
        @Name("waitValue.alias") public native @Cast("CUdeviceptr") long waitValue_alias(); public native CUstreamBatchMemOpParams waitValue_alias(long setter);
        @Name("writeValue.operation") public native @Cast("CUstreamBatchMemOpType") int writeValue_operation(); public native CUstreamBatchMemOpParams writeValue_operation(int setter);
        @Name("writeValue.address") public native @Cast("CUdeviceptr") long writeValue_address(); public native CUstreamBatchMemOpParams writeValue_address(long setter);
            @Name("writeValue.value") public native @Cast("cuuint32_t") int writeValue_value(); public native CUstreamBatchMemOpParams writeValue_value(int setter);
            @Name("writeValue.value64") public native @Cast("cuuint64_t") int writeValue_value64(); public native CUstreamBatchMemOpParams writeValue_value64(int setter);
        @Name("writeValue.flags") public native @Cast("unsigned int") int writeValue_flags(); public native CUstreamBatchMemOpParams writeValue_flags(int setter);
        /** For driver internal use. Initial value is unimportant. */
        @Name("writeValue.alias") public native @Cast("CUdeviceptr") long writeValue_alias(); public native CUstreamBatchMemOpParams writeValue_alias(long setter);
        @Name("flushRemoteWrites.operation") public native @Cast("CUstreamBatchMemOpType") int flushRemoteWrites_operation(); public native CUstreamBatchMemOpParams flushRemoteWrites_operation(int setter);
        @Name("flushRemoteWrites.flags") public native @Cast("unsigned int") int flushRemoteWrites_flags(); public native CUstreamBatchMemOpParams flushRemoteWrites_flags(int setter);
    public native @Cast("cuuint64_t") int pad(int i); public native CUstreamBatchMemOpParams pad(int i, int setter);
    @MemberGetter public native @Cast("cuuint64_t*") IntPointer pad();
}
