.PHONY: ALL

ALL: XRtrigo1.vo

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

XRfunctions.vo: XRfunctions.v XArithProp.vo
	C:\Coq\bin\coqc XRfunctions.v

XRseries.vo: XRseries.v XRfunctions.vo
	C:\Coq\bin\coqc XRseries.v

XSeqProp.vo: XSeqProp.v XRseries.vo
	C:\Coq\bin\coqc XSeqProp.v

XRcomplete.vo: XRcomplete.v XSeqProp.vo
	C:\Coq\bin\coqc XRcomplete.v

XPartSum.vo: XPartSum.v XRcomplete.vo
	C:\Coq\bin\coqc XPartSum.v

XAltSeries.vo: XAltSeries.v XPartSum.vo
	C:\Coq\bin\coqc XAltSeries.v

XBinomial.vo: XBinomial.v XAltSeries.vo
	C:\Coq\bin\coqc XBinomial.v

XRsigma.vo: XRsigma.v XBinomial.vo
	C:\Coq\bin\coqc XRsigma.v

XRprod.vo: XRprod.v XRsigma.vo
	C:\Coq\bin\coqc XRprod.v

XCauchy_prod.vo: XCauchy_prod.v XRprod.vo
	C:\Coq\bin\coqc XCauchy_prod.v

XAlembert.vo: XAlembert.v XCauchy_prod.vo
	C:\Coq\bin\coqc XAlembert.v
	
XSeqSeries.vo: XSeqSeries.v XAlembert.vo
	C:\Coq\bin\coqc XSeqSeries.v

XRtrigo_fun.vo: XRtrigo_fun.v XSeqSeries.vo
	C:\Coq\bin\coqc XRtrigo_fun.v

XRtrigo_def.vo: XRtrigo_def.v XRtrigo_fun.vo
	C:\Coq\bin\coqc XRtrigo_def.v

XRtrigo_alt.vo: XRtrigo_alt.v XRtrigo_def.vo
	C:\Coq\bin\coqc XRtrigo_alt.v

XCos_rel.vo: XCos_rel.v XRtrigo_alt.vo
	C:\Coq\bin\coqc XCos_rel.v

XCos_plus.vo: XCos_plus.v XCos_rel.vo
	C:\Coq\bin\coqc XCos_plus.v

XRlimit.vo: XRlimit.v XCos_plus.vo
	C:\Coq\bin\coqc XRlimit.v

XRderiv.vo: XRderiv.v XRlimit.vo
	C:\Coq\bin\coqc XRderiv.v

XRanalysis1.vo: XRanalysis1.v XRderiv.vo
	C:\Coq\bin\coqc XRanalysis1.v

XRsqrt_def.vo: XRsqrt_def.v XRanalysis1.vo
	C:\Coq\bin\coqc XRsqrt_def.v

XRList.vo: XRList.v XRsqrt_def.vo
	C:\Coq\bin\coqc XRList.v

XRtopology.vo: XRtopology.v XRList.vo
	C:\Coq\bin\coqc XRtopology.v

XMVT.vo: XMVT.v XRtopology.vo
	C:\Coq\bin\coqc XMVT.v

XPSeries_reg.vo: XPSeries_reg.v XMVT.vo
	C:\Coq\bin\coqc XPSeries_reg.v

XRtrigo1.vo: XRtrigo1.v XPSeries_reg.vo
	C:\Coq\bin\coqc XRtrigo1.v

#.vo: .v .vo
#	C:\Coq\bin\coqc .v
