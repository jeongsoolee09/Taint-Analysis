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
public class NodeDef_ExperimentalDebugInfo extends MessageLite {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public NodeDef_ExperimentalDebugInfo(Pointer p) { super(p); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public NodeDef_ExperimentalDebugInfo(long size) { super((Pointer)null); allocateArray(size); }
    private native void allocateArray(long size);
    @Override public NodeDef_ExperimentalDebugInfo position(long position) {
        return (NodeDef_ExperimentalDebugInfo)super.position(position);
    }
    @Override public NodeDef_ExperimentalDebugInfo getPointer(long i) {
        return new NodeDef_ExperimentalDebugInfo(this).position(position + i);
    }

  public NodeDef_ExperimentalDebugInfo() { super((Pointer)null); allocate(); }
  private native void allocate();

  public NodeDef_ExperimentalDebugInfo(@Const @ByRef NodeDef_ExperimentalDebugInfo from) { super((Pointer)null); allocate(from); }
  private native void allocate(@Const @ByRef NodeDef_ExperimentalDebugInfo from);

  public native @ByRef @Name("operator =") NodeDef_ExperimentalDebugInfo put(@Const @ByRef NodeDef_ExperimentalDebugInfo from);

  public native Arena GetArena();
  public native Pointer GetMaybeArenaPointer();
  public static native @Cast("const google::protobuf::Descriptor*") Pointer descriptor();
  public static native @Cast("const google::protobuf::Descriptor*") Pointer GetDescriptor();
  public static native @Cast("const google::protobuf::Reflection*") Pointer GetReflection();
  public static native @Const @ByRef NodeDef_ExperimentalDebugInfo default_instance();

  public static native void InitAsDefaultInstance();  // FOR INTERNAL USE ONLY
  public static native @Const NodeDef_ExperimentalDebugInfo internal_default_instance();
  @MemberGetter public static native int kIndexInFileMessages();
  public static final int kIndexInFileMessages = kIndexInFileMessages();

  public native void UnsafeArenaSwap(NodeDef_ExperimentalDebugInfo other);
  public native void Swap(NodeDef_ExperimentalDebugInfo other);
  

  // implements Message ----------------------------------------------

  public native NodeDef_ExperimentalDebugInfo New();

  public native NodeDef_ExperimentalDebugInfo New(Arena arena);
  public native void CopyFrom(@Cast("const google::protobuf::Message*") @ByRef MessageLite from);
  public native void MergeFrom(@Cast("const google::protobuf::Message*") @ByRef MessageLite from);
  public native void CopyFrom(@Const @ByRef NodeDef_ExperimentalDebugInfo from);
  public native void MergeFrom(@Const @ByRef NodeDef_ExperimentalDebugInfo from);
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

  // repeated string original_node_names = 1;
  public native int original_node_names_size();
  public native void clear_original_node_names();
  @MemberGetter public static native int kOriginalNodeNamesFieldNumber();
  public static final int kOriginalNodeNamesFieldNumber = kOriginalNodeNamesFieldNumber();
  public native @StdString BytePointer original_node_names(int index);
  public native @StdString @Cast({"char*", "std::string*"}) BytePointer mutable_original_node_names(int index);
  public native void set_original_node_names(int index, @StdString BytePointer value);
  public native void set_original_node_names(int index, @StdString String value);
  public native void set_original_node_names(int index, @Cast("const char*") BytePointer value, @Cast("size_t") long size);
  public native void set_original_node_names(int index, String value, @Cast("size_t") long size);
  public native @StdString @Cast({"char*", "std::string*"}) BytePointer add_original_node_names();
  public native void add_original_node_names(@StdString BytePointer value);
  public native void add_original_node_names(@StdString String value);
  public native void add_original_node_names(@Cast("const char*") BytePointer value, @Cast("size_t") long size);
  public native void add_original_node_names(String value, @Cast("size_t") long size);

  // repeated string original_func_names = 2;
  public native int original_func_names_size();
  public native void clear_original_func_names();
  @MemberGetter public static native int kOriginalFuncNamesFieldNumber();
  public static final int kOriginalFuncNamesFieldNumber = kOriginalFuncNamesFieldNumber();
  public native @StdString BytePointer original_func_names(int index);
  public native @StdString @Cast({"char*", "std::string*"}) BytePointer mutable_original_func_names(int index);
  public native void set_original_func_names(int index, @StdString BytePointer value);
  public native void set_original_func_names(int index, @StdString String value);
  public native void set_original_func_names(int index, @Cast("const char*") BytePointer value, @Cast("size_t") long size);
  public native void set_original_func_names(int index, String value, @Cast("size_t") long size);
  public native @StdString @Cast({"char*", "std::string*"}) BytePointer add_original_func_names();
  public native void add_original_func_names(@StdString BytePointer value);
  public native void add_original_func_names(@StdString String value);
  public native void add_original_func_names(@Cast("const char*") BytePointer value, @Cast("size_t") long size);
  public native void add_original_func_names(String value, @Cast("size_t") long size);
}
