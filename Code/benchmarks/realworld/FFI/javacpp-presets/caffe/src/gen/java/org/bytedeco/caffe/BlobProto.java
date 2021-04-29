// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.caffe;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;
import static org.bytedeco.openblas.global.openblas_nolapack.*;
import static org.bytedeco.openblas.global.openblas.*;
import org.bytedeco.opencv.opencv_core.*;
import static org.bytedeco.opencv.global.opencv_core.*;
import org.bytedeco.opencv.opencv_imgproc.*;
import static org.bytedeco.opencv.global.opencv_imgproc.*;
import static org.bytedeco.opencv.global.opencv_imgcodecs.*;
import org.bytedeco.opencv.opencv_videoio.*;
import static org.bytedeco.opencv.global.opencv_videoio.*;
import org.bytedeco.opencv.opencv_highgui.*;
import static org.bytedeco.opencv.global.opencv_highgui.*;
import org.bytedeco.hdf5.*;
import static org.bytedeco.hdf5.global.hdf5.*;

import static org.bytedeco.caffe.global.caffe.*;

// -------------------------------------------------------------------

@Namespace("caffe") @NoOffset @Properties(inherit = org.bytedeco.caffe.presets.caffe.class)
public class BlobProto extends Message {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public BlobProto(Pointer p) { super(p); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public BlobProto(long size) { super((Pointer)null); allocateArray(size); }
    private native void allocateArray(long size);
    @Override public BlobProto position(long position) {
        return (BlobProto)super.position(position);
    }
    @Override public BlobProto getPointer(long i) {
        return new BlobProto(this).position(position + i);
    }

  public BlobProto() { super((Pointer)null); allocate(); }
  private native void allocate();

  public BlobProto(@Const @ByRef BlobProto from) { super((Pointer)null); allocate(from); }
  private native void allocate(@Const @ByRef BlobProto from);

  public native @ByRef @Name("operator =") BlobProto put(@Const @ByRef BlobProto from);
//   #if LANG_CXX11
//   #endif
  public native @Const @ByRef UnknownFieldSet unknown_fields();
  public native UnknownFieldSet mutable_unknown_fields();

  public static native @Const Descriptor descriptor();
  public static native @Const @ByRef BlobProto default_instance();

  public static native void InitAsDefaultInstance();  // FOR INTERNAL USE ONLY
  public static native @Const BlobProto internal_default_instance();
  @MemberGetter public static native int kIndexInFileMessages();
  public static final int kIndexInFileMessages = kIndexInFileMessages();

  public native void Swap(BlobProto other);
  

  // implements Message ----------------------------------------------

  public native final BlobProto New();

  public native final BlobProto New(Arena arena);
  public native final void CopyFrom(@Const @ByRef Message from);
  public native final void MergeFrom(@Const @ByRef Message from);
  public native void CopyFrom(@Const @ByRef BlobProto from);
  public native void MergeFrom(@Const @ByRef BlobProto from);
  public native final void Clear();
  public native @Cast("bool") final boolean IsInitialized();

  public native @Cast("size_t") final long ByteSizeLong();
//   #if GOOGLE_PROTOBUF_ENABLE_EXPERIMENTAL_PARSER
//   #else
  public native @Cast("bool") final boolean MergePartialFromCodedStream(
        CodedInputStream input);
//   #endif  // GOOGLE_PROTOBUF_ENABLE_EXPERIMENTAL_PARSER
  public native final void SerializeWithCachedSizes(
        CodedOutputStream output);
  public native @Cast("google::protobuf::uint8*") final BytePointer InternalSerializeWithCachedSizesToArray(
        @Cast("google::protobuf::uint8*") BytePointer target);
  public native @Cast("google::protobuf::uint8*") final ByteBuffer InternalSerializeWithCachedSizesToArray(
        @Cast("google::protobuf::uint8*") ByteBuffer target);
  public native @Cast("google::protobuf::uint8*") final byte[] InternalSerializeWithCachedSizesToArray(
        @Cast("google::protobuf::uint8*") byte[] target);
  public native final int GetCachedSize();

  public native @ByVal final Metadata GetMetadata();

  // nested types ----------------------------------------------------

  // accessors -------------------------------------------------------

  // repeated float data = 5 [packed = true];
  public native int data_size();
  public native void clear_data();
  @MemberGetter public static native int kDataFieldNumber();
  public static final int kDataFieldNumber = kDataFieldNumber();
  public native float data(int index);
  public native void set_data(int index, float value);
  public native void add_data(float value);

  // repeated float diff = 6 [packed = true];
  public native int diff_size();
  public native void clear_diff();
  @MemberGetter public static native int kDiffFieldNumber();
  public static final int kDiffFieldNumber = kDiffFieldNumber();
  public native float diff(int index);
  public native void set_diff(int index, float value);
  public native void add_diff(float value);

  // repeated double double_data = 8 [packed = true];
  public native int double_data_size();
  public native void clear_double_data();
  @MemberGetter public static native int kDoubleDataFieldNumber();
  public static final int kDoubleDataFieldNumber = kDoubleDataFieldNumber();
  public native double double_data(int index);
  public native void set_double_data(int index, double value);
  public native void add_double_data(double value);

  // repeated double double_diff = 9 [packed = true];
  public native int double_diff_size();
  public native void clear_double_diff();
  @MemberGetter public static native int kDoubleDiffFieldNumber();
  public static final int kDoubleDiffFieldNumber = kDoubleDiffFieldNumber();
  public native double double_diff(int index);
  public native void set_double_diff(int index, double value);
  public native void add_double_diff(double value);

  // optional .caffe.BlobShape shape = 7;
  public native @Cast("bool") boolean has_shape();
  public native void clear_shape();
  @MemberGetter public static native int kShapeFieldNumber();
  public static final int kShapeFieldNumber = kShapeFieldNumber();
  public native @Const @ByRef BlobShape shape();
  public native BlobShape release_shape();
  public native BlobShape mutable_shape();
  public native void set_allocated_shape(BlobShape shape);

  // optional int32 num = 1 [default = 0];
  public native @Cast("bool") boolean has_num();
  public native void clear_num();
  @MemberGetter public static native int kNumFieldNumber();
  public static final int kNumFieldNumber = kNumFieldNumber();
  public native @Cast("google::protobuf::int32") int num();
  public native void set_num(@Cast("google::protobuf::int32") int value);

  // optional int32 channels = 2 [default = 0];
  public native @Cast("bool") boolean has_channels();
  public native void clear_channels();
  @MemberGetter public static native int kChannelsFieldNumber();
  public static final int kChannelsFieldNumber = kChannelsFieldNumber();
  public native @Cast("google::protobuf::int32") int channels();
  public native void set_channels(@Cast("google::protobuf::int32") int value);

  // optional int32 height = 3 [default = 0];
  public native @Cast("bool") boolean has_height();
  public native void clear_height();
  @MemberGetter public static native int kHeightFieldNumber();
  public static final int kHeightFieldNumber = kHeightFieldNumber();
  public native @Cast("google::protobuf::int32") int height();
  public native void set_height(@Cast("google::protobuf::int32") int value);

  // optional int32 width = 4 [default = 0];
  public native @Cast("bool") boolean has_width();
  public native void clear_width();
  @MemberGetter public static native int kWidthFieldNumber();
  public static final int kWidthFieldNumber = kWidthFieldNumber();
  public native @Cast("google::protobuf::int32") int width();
  public native void set_width(@Cast("google::protobuf::int32") int value);
}
