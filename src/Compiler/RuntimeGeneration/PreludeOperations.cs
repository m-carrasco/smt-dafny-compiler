namespace SDC.Converter;

using System.Collections.Generic;
using SDC.AST;
using SDC.Stubs;

public static class PreludeOperations
{
    public readonly static List<Func<TypeReference, MethodDefinition>> MethodBuilders = new() {
        SafeUnsignedDiv.GetSafeDivMethodCode,
        SafeSignedDiv.GetSafeDivMethodCode,
    };

    public readonly static List<Func<TypeReference, FunctionDefinition>> FunctionBuilders = new() {
        SafeUnsignedDiv.GetSafeDivFunctionCode,
        SafeSignedDiv.GetSafeDivFunctionCode,
    };
}
