// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.hdf5;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.hdf5.global.hdf5.*;


/** \class DSetMemXferPropList
    \brief Class DSetCreatPropList inherits from PropList and provides
    wrappers for the HDF5 dataset memory and transfer property list.
*/
//  Inheritance: PropList -> IdComponent
@Namespace("H5") @NoOffset @Properties(inherit = org.bytedeco.hdf5.presets.hdf5.class)
public class DSetMemXferPropList extends PropList {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public DSetMemXferPropList(Pointer p) { super(p); }

        /**\brief Default dataset memory and transfer property list. */
        @MemberGetter public static native @Const @ByRef DSetMemXferPropList DEFAULT();

        // Creates a dataset memory and transfer property list.
        public DSetMemXferPropList() { super((Pointer)null); allocate(); }
        private native void allocate();

        // Creates a dataset transform property list.
        public DSetMemXferPropList(@Cast("const char*") BytePointer expression) { super((Pointer)null); allocate(expression); }
        private native void allocate(@Cast("const char*") BytePointer expression);
        public DSetMemXferPropList(String expression) { super((Pointer)null); allocate(expression); }
        private native void allocate(String expression);

        // Sets type conversion and background buffers.
        public native void setBuffer(@Cast("size_t") long size, Pointer tconv, Pointer bkg);

        // Reads buffer settings.
        public native @Cast("size_t") long getBuffer(@Cast("void**") PointerPointer tconv, @Cast("void**") PointerPointer bkg);
        public native @Cast("size_t") long getBuffer(@Cast("void**") @ByPtrPtr Pointer tconv, @Cast("void**") @ByPtrPtr Pointer bkg);

        // Sets B-tree split ratios for a dataset transfer property list.
        public native void setBtreeRatios(double left, double middle, double right);

        // Gets B-tree split ratios for a dataset transfer property list.
        public native void getBtreeRatios(@ByRef DoublePointer left, @ByRef DoublePointer middle, @ByRef DoublePointer right);
        public native void getBtreeRatios(@ByRef DoubleBuffer left, @ByRef DoubleBuffer middle, @ByRef DoubleBuffer right);
        public native void getBtreeRatios(@ByRef double[] left, @ByRef double[] middle, @ByRef double[] right);

        // Sets data transform expression.
        public native void setDataTransform(@Cast("const char*") BytePointer expression);
        public native void setDataTransform(String expression);

        // Gets data transform expression.
        public native @Cast("ssize_t") long getDataTransform(@Cast("char*") BytePointer exp, @Cast("size_t") long buf_size/*=0*/);
        public native @Cast("ssize_t") long getDataTransform(@Cast("char*") BytePointer exp);
        public native @Cast("ssize_t") long getDataTransform(@Cast("char*") ByteBuffer exp, @Cast("size_t") long buf_size/*=0*/);
        public native @Cast("ssize_t") long getDataTransform(@Cast("char*") ByteBuffer exp);
        public native @Cast("ssize_t") long getDataTransform(@Cast("char*") byte[] exp, @Cast("size_t") long buf_size/*=0*/);
        public native @Cast("ssize_t") long getDataTransform(@Cast("char*") byte[] exp);
        public native @StdString BytePointer getDataTransform();

        // Sets the dataset transfer property list status to TRUE or FALSE.
        public native void setPreserve(@Cast("bool") boolean status);

        // Checks status of the dataset transfer property list.
        public native @Cast("bool") boolean getPreserve();

        // Sets an exception handling callback for datatype conversion.
        public native void setTypeConvCB(H5T_conv_except_func_t op, Pointer user_data);

        // Gets the exception handling callback for datatype conversion.
        public native void getTypeConvCB(@ByPtrPtr H5T_conv_except_func_t op, @Cast("void**") PointerPointer user_data);
        public native void getTypeConvCB(@ByPtrPtr H5T_conv_except_func_t op, @Cast("void**") @ByPtrPtr Pointer user_data);

        // Sets the memory manager for variable-length datatype
        // allocation in H5Dread and H5Treclaim.
        public native void setVlenMemManager(H5MM_allocate_t alloc, Pointer alloc_info,
                                       H5MM_free_t _free, Pointer free_info);

        // alloc and free are set to NULL, indicating that system
        // malloc and free are to be used.
        public native void setVlenMemManager();

        // Gets the memory manager for variable-length datatype
        // allocation in H5Dread and H5Treclaim.
        public native void getVlenMemManager(@ByPtrRef H5MM_allocate_t alloc, @Cast("void**") PointerPointer alloc_info,
                                       @ByPtrRef H5MM_free_t _free, @Cast("void**") PointerPointer free_info);
        public native void getVlenMemManager(@ByPtrRef H5MM_allocate_t alloc, @Cast("void**") @ByPtrPtr Pointer alloc_info,
                                       @ByPtrRef H5MM_free_t _free, @Cast("void**") @ByPtrPtr Pointer free_info);

        // Sets the size of a contiguous block reserved for small data.
        public native void setSmallDataBlockSize(@Cast("hsize_t") long size);

        // Returns the current small data block size setting.
        public native @Cast("hsize_t") long getSmallDataBlockSize();

        // Sets number of I/O vectors to be read/written in hyperslab I/O.
        public native void setHyperVectorSize(@Cast("size_t") long vector_size);

        // Returns the number of I/O vectors to be read/written in
        // hyperslab I/O.
        public native @Cast("size_t") long getHyperVectorSize();

        // Enables or disables error-detecting for a dataset reading
        // process.
        public native void setEDCCheck(@Cast("H5Z_EDC_t") int check);

        // Determines whether error-detection is enabled for dataset reads.
        public native @Cast("H5Z_EDC_t") int getEDCCheck();

        /**\brief Returns this class name. */
        public native @StdString BytePointer fromClass();

        // Copy constructor - same as the original DSetMemXferPropList.
        public DSetMemXferPropList(@Const @ByRef DSetMemXferPropList orig) { super((Pointer)null); allocate(orig); }
        private native void allocate(@Const @ByRef DSetMemXferPropList orig);

        // Creates a copy of an existing dataset memory and transfer
        // property list using the property list id.
        public DSetMemXferPropList(@Cast("const hid_t") long plist_id) { super((Pointer)null); allocate(plist_id); }
        private native void allocate(@Cast("const hid_t") long plist_id);

        // Noop destructor

// #ifndef DOXYGEN_SHOULD_SKIP_THIS

        // Deletes the global constant, should only be used by the library
        public static native void deleteConstants();

}
