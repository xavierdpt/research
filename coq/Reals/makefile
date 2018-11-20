.PHONY: ALL

ALL: XArithProp.vo

XRdefinitions.vo: XRdefinitions.v
	C:\Coq\bin\coqc XRdefinitions.v

XRaxioms.vo: XRaxioms.v XRdefinitions.vo
	C:\Coq\bin\coqc XRaxioms.v

XRpow_def.vo: XRpow_def.v XRaxioms.vo
	C:\Coq\bin\coqc XRpow_def.v

XRIneq.vo: XRIneq.v XRpow_def.vo
	C:\Coq\bin\coqc XRIneq.v

XDiscrR.vo: XDiscrR.v XRIneq.vo
	C:\Coq\bin\coqc XDiscrR.v

XRbase.vo: XRbase.v XDiscrR.vo
	C:\Coq\bin\coqc XRbase.v

XR_Ifp.vo: XR_Ifp.v XRbase.vo
	C:\Coq\bin\coqc XR_Ifp.v


XRbasic_fun.vo: XRbasic_fun.v XR_Ifp.vo
	C:\Coq\bin\coqc XRbasic_fun.v

XR_sqr.vo: XR_sqr.v XRbasic_fun.vo
	C:\Coq\bin\coqc XR_sqr.v

XSplitAbsolu.vo: XSplitAbsolu.v XR_sqr.vo
	C:\Coq\bin\coqc XSplitAbsolu.v

XSplitRmult.vo: XSplitRmult.v XSplitAbsolu.vo
	C:\Coq\bin\coqc XSplitRmult.v

XArithProp.vo: XArithProp.v XSplitRmult.vo
	C:\Coq\bin\coqc XArithProp.v


#.vo: .v .vo
#	C:\Coq\bin\coqc .v
