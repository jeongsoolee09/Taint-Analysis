// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.tensorflow;

import org.bytedeco.tensorflow.Allocator;
import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.tensorflow.global.tensorflow.*;

// -------------------------------------------------------------------

@Namespace("tensorflow") @NoOffset @Properties(inherit = org.bytedeco.tensorflow.presets.tensorflow.class)
public class SavedAsset extends MessageLite {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public SavedAsset(Pointer p) { super(p); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public SavedAsset(long size) { super((Pointer)null); allocateArray(size); }
    private native void allocateArray(long size);
    @Override public SavedAsset position(long position) {
        return (SavedAsset)super.position(position);
    }
    @Override public SavedAsset getPointer(long i) {
        return new SavedAsset(this).position(position + i);
    }

  public SavedAsset() { super((Pointer)null); allocate(); }
  private native void allocate();

  public SavedAsset(@Const @ByRef SavedAsset from) { super((Pointer)null); allocate(from); }
  private native void allocate(@Const @ByRef SavedAsset from);

  public native @ByRef @Name("operator =") SavedAsset put(@Const @ByRef SavedAsset from);

  public native Arena GetArena();
  public native Pointer GetMaybeArenaPointer();
  public static native @Cast("const google::protobuf::Descriptor*") Pointer descriptor();
  public static native @Cast("const google::protobuf::Descriptor*") Pointer GetDescriptor();
  public static native @Cast("const google::protobuf::Reflection*") Pointer GetReflection();
  public static native @Const @ByRef SavedAsset default_instance();

  public static native void InitAsDefaultInstance();  // FOR INTERNAL USE ONLY
  public static native @Const SavedAsset internal_default_instance();
  @MemberGetter public static native int kIndexInFileMessages();
  public static final int kIndexInFileMessages = kIndexInFileMessages();

  public native void UnsafeArenaSwap(SavedAsset other);
  public native void Swap(SavedAsset other);
  

  // implements Message ----------------------------------------------

  public native SavedAsset New();

  public native SavedAsset New(Arena arena);
  public native void CopyFrom(@Cast("const google::protobuf::Message*") @ByRef MessageLite from);
  public native void MergeFrom(@Cast("const google::protobuf::Message*") @ByRef MessageLite from);
  public native void CopyFrom(@Const @ByRef SavedAsset from);
  public native void MergeFrom(@Const @ByRef SavedAsset from);
  public native void Clear();
  public native @Cast("bool") boolean IsInitialized();

  public native @Cast("size_t") long ByteSizeLong();
//   #if GOOGLE_PROTOBUF_ENABLE_EXPERIMENTAL_PARSER
//   #else
  public native @Cast("bool") boolean MergePartialFromCodedStream(
        CodedInputStream input);
//   #endif  // GOOGLE_PROTOBUF_ENABLE_EXPERIMENTAL_PARSER
  public native void SerializeWithCachedSizes(
        CodedOutputStream output);
  public native @Cast("google::protobuf::uint8*") BytePointer InternalSerializeWithCachedSizesToArray(
        @Cast("google::protobuf::uint8*") BytePointer target);
  public native @Cast("google::protobuf::uint8*") ByteBuffer InternalSerializeWithCachedSizesToArray(
        @Cast("google::protobuf::uint8*") ByteBuffer target);
  public native @Cast("google::protobuf::uint8*") byte[] InternalSerializeWithCachedSizesToArray(
        @Cast("google::protobuf::uint8*") byte[] target);
  public native int GetCachedSize();

  public native @ByVal @Cast("google::protobuf::Metadata*") Pointer GetMetadata();

  // nested types ----------------------------------------------------

  // accessors -------------------------------------------------------

  // int32 asset_file_def_index = 1;
  public native void clear_asset_file_def_index();
  @MemberGetter public static native int kAssetFileDefIndexFieldNumber();
  public static final int kAssetFileDefIndexFieldNumber = kAssetFileDefIndexFieldNumber();
  public native @Cast("google::protobuf::int32") int asset_file_def_index();
  public native void set_asset_file_def_index(@Cast("google::protobuf::int32") int value);
}
