// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.cuda.cudart;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.cuda.global.cudart.*;


/**
 * External semaphore wait parameters
 */
@Properties(inherit = org.bytedeco.cuda.presets.cudart.class)
public class CUDA_EXTERNAL_SEMAPHORE_WAIT_PARAMS extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public CUDA_EXTERNAL_SEMAPHORE_WAIT_PARAMS() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public CUDA_EXTERNAL_SEMAPHORE_WAIT_PARAMS(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public CUDA_EXTERNAL_SEMAPHORE_WAIT_PARAMS(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public CUDA_EXTERNAL_SEMAPHORE_WAIT_PARAMS position(long position) {
        return (CUDA_EXTERNAL_SEMAPHORE_WAIT_PARAMS)super.position(position);
    }
    @Override public CUDA_EXTERNAL_SEMAPHORE_WAIT_PARAMS getPointer(long i) {
        return new CUDA_EXTERNAL_SEMAPHORE_WAIT_PARAMS((Pointer)this).position(position + i);
    }

        /**
         * Parameters for fence objects
         */
            /**
             * Value of fence to be waited on
             */
            @Name("params.fence.value") public native @Cast("unsigned long long") long params_fence_value(); public native CUDA_EXTERNAL_SEMAPHORE_WAIT_PARAMS params_fence_value(long setter);
        /**
         * Pointer to NvSciSyncFence. Valid if CUexternalSemaphoreHandleType
         * is of type CU_EXTERNAL_SEMAPHORE_HANDLE_TYPE_NVSCISYNC.
         */
            @Name("params.nvSciSync.fence") public native Pointer params_nvSciSync_fence(); public native CUDA_EXTERNAL_SEMAPHORE_WAIT_PARAMS params_nvSciSync_fence(Pointer setter);
            @Name("params.nvSciSync.reserved") public native @Cast("unsigned long long") long params_nvSciSync_reserved(); public native CUDA_EXTERNAL_SEMAPHORE_WAIT_PARAMS params_nvSciSync_reserved(long setter);
        /**
         * Parameters for keyed mutex objects
         */
            /**
             * Value of key to acquire the mutex with
             */
            @Name("params.keyedMutex.key") public native @Cast("unsigned long long") long params_keyedMutex_key(); public native CUDA_EXTERNAL_SEMAPHORE_WAIT_PARAMS params_keyedMutex_key(long setter);
            /**
             * Timeout in milliseconds to wait to acquire the mutex
             */
            @Name("params.keyedMutex.timeoutMs") public native @Cast("unsigned int") int params_keyedMutex_timeoutMs(); public native CUDA_EXTERNAL_SEMAPHORE_WAIT_PARAMS params_keyedMutex_timeoutMs(int setter);
        @Name("params.reserved") public native @Cast("unsigned int") int params_reserved(int i); public native CUDA_EXTERNAL_SEMAPHORE_WAIT_PARAMS params_reserved(int i, int setter);
        @Name("params.reserved") @MemberGetter public native @Cast("unsigned int*") IntPointer params_reserved();
    /**
     * Only when ::CUDA_EXTERNAL_SEMAPHORE_WAIT_PARAMS is used to wait on
     * a ::CUexternalSemaphore of type ::CU_EXTERNAL_SEMAPHORE_HANDLE_TYPE_NVSCISYNC,
     * the valid flag is ::CUDA_EXTERNAL_SEMAPHORE_WAIT_SKIP_NVSCIBUF_MEMSYNC
     * which indicates that while waiting for the ::CUexternalSemaphore, no memory
     * synchronization operations should be performed for any external memory
     * object imported as ::CU_EXTERNAL_MEMORY_HANDLE_TYPE_NVSCIBUF.
     * For all other types of ::CUexternalSemaphore, flags must be zero.
     */
    public native @Cast("unsigned int") int flags(); public native CUDA_EXTERNAL_SEMAPHORE_WAIT_PARAMS flags(int setter);
    public native @Cast("unsigned int") int reserved(int i); public native CUDA_EXTERNAL_SEMAPHORE_WAIT_PARAMS reserved(int i, int setter);
    @MemberGetter public native @Cast("unsigned int*") IntPointer reserved();
}