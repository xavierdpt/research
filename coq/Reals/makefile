.PHONY: ALL

ALL: XRtrigo_def.vo Rtrigo.vo Rpower.vo XRanalysis1.vo ROrderedType.vo XRbasic_fun.vo Ranalysis2.vo XRtrigo_fun.vo XRIneq.vo XRList.vo XRpow_def.vo XSplitAbsolu.vo XPSeries_reg.vo XSeqProp.vo NewtonInt.vo XSeqSeries.vo Ranalysis3.vo XRsigma.vo XRtopology.vo XR_sqr.vo XAltSeries.vo XRcomplete.vo RiemannInt.vo XCos_rel.vo Experiment.vo Rtrigo_calc.vo Exp_prop.vo Rtrigo_reg.vo Ranalysis_reg.vo Rminmax.vo XSplitRmult.vo XRprod.vo Rlimit.vo RiemannInt_SF.vo XRfunctions.vo XDiscrR.vo Machin.vo Ranalysis4.vo XArithProp.vo XRlimit.vo Integration.vo XRderiv.vo XPartSum.vo XR_Ifp.vo XCos_plus.vo XAlembert.vo XRaxioms.vo XRsqrt_def.vo XCauchy_prod.vo Ratan.vo R_sqrt.vo Rlogic.vo XBinomial.vo XRbase.vo Ranalysis.vo Reals.vo Rgeom.vo Ranalysis5.vo XRtrigo_alt.vo XMVT.vo XRdefinitions.vo XRseries.vo Sqrt_reg.vo XRtrigo1.vo

Experiment.vo : Experiment.v  Reals.vo
	 C:\Coq\bin\coqc Experiment.v

Exp_prop.vo : Exp_prop.v 
	 C:\Coq\bin\coqc Exp_prop.v

Integration.vo : Integration.v  NewtonInt.vo RiemannInt_SF.vo RiemannInt.vo
	 C:\Coq\bin\coqc Integration.v

Machin.vo : Machin.v  Ranalysis_reg.vo Ratan.vo
	 C:\Coq\bin\coqc Machin.v

NewtonInt.vo : NewtonInt.v  Ranalysis.vo
	 C:\Coq\bin\coqc NewtonInt.v

Ranalysis.vo : Ranalysis.v  Rtrigo.vo Ranalysis2.vo Ranalysis3.vo Exp_prop.vo Rtrigo_reg.vo R_sqrt.vo Rtrigo_calc.vo Rgeom.vo Sqrt_reg.vo Ranalysis4.vo Rpower.vo Ranalysis_reg.vo
	 C:\Coq\bin\coqc Ranalysis.v

Ranalysis2.vo : Ranalysis2.v 
	 C:\Coq\bin\coqc Ranalysis2.v

Ranalysis3.vo : Ranalysis3.v  Ranalysis2.vo
	 C:\Coq\bin\coqc Ranalysis3.v

Ranalysis4.vo : Ranalysis4.v  Ranalysis3.vo Exp_prop.vo
	 C:\Coq\bin\coqc Ranalysis4.v

Ranalysis5.vo : Ranalysis5.v  Ranalysis_reg.vo RiemannInt.vo
	 C:\Coq\bin\coqc Ranalysis5.v

Ranalysis_reg.vo : Ranalysis_reg.v  Ranalysis2.vo Ranalysis3.vo Exp_prop.vo Rtrigo_reg.vo R_sqrt.vo Rtrigo_calc.vo Rgeom.vo Sqrt_reg.vo Ranalysis4.vo Rpower.vo
	 C:\Coq\bin\coqc Ranalysis_reg.v

Ratan.vo : Ratan.v  Ranalysis_reg.vo Ranalysis5.vo
	 C:\Coq\bin\coqc Ratan.v

Reals.vo : Reals.v  XRbase.vo XRfunctions.vo XSeqSeries.vo Rtrigo.vo Ranalysis.vo Integration.vo
	 C:\Coq\bin\coqc Reals.v

Rgeom.vo : Rgeom.v  R_sqrt.vo
	 C:\Coq\bin\coqc Rgeom.v

RiemannInt.vo : RiemannInt.v  Ranalysis_reg.vo RiemannInt_SF.vo
	 C:\Coq\bin\coqc RiemannInt.v

RiemannInt_SF.vo : RiemannInt_SF.v  Ranalysis_reg.vo
	 C:\Coq\bin\coqc RiemannInt_SF.v

Rlimit.vo : Rlimit.v 
	 C:\Coq\bin\coqc Rlimit.v

Rlogic.vo : Rlogic.v 
	 C:\Coq\bin\coqc Rlogic.v

Rminmax.vo : Rminmax.v  ROrderedType.vo
	 C:\Coq\bin\coqc Rminmax.v

ROrderedType.vo : ROrderedType.v 
	 C:\Coq\bin\coqc ROrderedType.v

Rpower.vo : Rpower.v  Exp_prop.vo R_sqrt.vo Sqrt_reg.vo Ranalysis4.vo
	 C:\Coq\bin\coqc Rpower.v

Rtrigo.vo : Rtrigo.v  XRbase.vo XRfunctions.vo XSeqSeries.vo XRtrigo_fun.vo XRtrigo_def.vo XRtrigo_alt.vo XCos_rel.vo XCos_plus.vo XRanalysis1.vo XRsqrt_def.vo XPSeries_reg.vo Ratan.vo Machin.vo
	 C:\Coq\bin\coqc Rtrigo.v

Rtrigo_calc.vo : Rtrigo_calc.v  R_sqrt.vo
	 C:\Coq\bin\coqc Rtrigo_calc.v

Rtrigo_reg.vo : Rtrigo_reg.v 
	 C:\Coq\bin\coqc Rtrigo_reg.v

R_sqrt.vo : R_sqrt.v 
	 C:\Coq\bin\coqc R_sqrt.v

Sqrt_reg.vo : Sqrt_reg.v  R_sqrt.vo
	 C:\Coq\bin\coqc Sqrt_reg.v

XAlembert.vo : XAlembert.v  XRbase.vo XRfunctions.vo XRseries.vo XSeqProp.vo XPartSum.vo
	 C:\Coq\bin\coqc XAlembert.v

XAltSeries.vo : XAltSeries.v  XRbase.vo XRfunctions.vo XRseries.vo XSeqProp.vo XPartSum.vo
	 C:\Coq\bin\coqc XAltSeries.v

XArithProp.vo : XArithProp.v  XRbase.vo XRbasic_fun.vo
	 C:\Coq\bin\coqc XArithProp.v

XBinomial.vo : XBinomial.v  XRbase.vo XRfunctions.vo XPartSum.vo
	 C:\Coq\bin\coqc XBinomial.v

XCauchy_prod.vo : XCauchy_prod.v  XRbase.vo XRfunctions.vo XRseries.vo XPartSum.vo
	 C:\Coq\bin\coqc XCauchy_prod.v

XCos_plus.vo : XCos_plus.v  XRbase.vo XRfunctions.vo XSeqSeries.vo XRtrigo_def.vo XCos_rel.vo
	 C:\Coq\bin\coqc XCos_plus.v

XCos_rel.vo : XCos_rel.v  XRbase.vo XRfunctions.vo XSeqSeries.vo XRtrigo_def.vo
	 C:\Coq\bin\coqc XCos_rel.v

XDiscrR.vo : XDiscrR.v  XRIneq.vo
	 C:\Coq\bin\coqc XDiscrR.v

XMVT.vo : XMVT.v  XRbase.vo XRfunctions.vo XRanalysis1.vo XRtopology.vo
	 C:\Coq\bin\coqc XMVT.v

XPartSum.vo : XPartSum.v  XRbase.vo XRfunctions.vo XRseries.vo XRcomplete.vo
	 C:\Coq\bin\coqc XPartSum.v

XPSeries_reg.vo : XPSeries_reg.v  XRbase.vo XRfunctions.vo XSeqSeries.vo XRanalysis1.vo XMVT.vo
	 C:\Coq\bin\coqc XPSeries_reg.v

XRanalysis1.vo : XRanalysis1.v  XRbase.vo XRfunctions.vo XRlimit.vo XRderiv.vo
	 C:\Coq\bin\coqc XRanalysis1.v

XRaxioms.vo : XRaxioms.v  XRdefinitions.vo
	 C:\Coq\bin\coqc XRaxioms.v

XRbase.vo : XRbase.v  XRdefinitions.vo XRaxioms.vo XRIneq.vo XDiscrR.vo
	 C:\Coq\bin\coqc XRbase.v

XRbasic_fun.vo : XRbasic_fun.v  XRbase.vo XR_Ifp.vo
	 C:\Coq\bin\coqc XRbasic_fun.v

XRcomplete.vo : XRcomplete.v  XRbase.vo XRfunctions.vo XRseries.vo XSeqProp.vo
	 C:\Coq\bin\coqc XRcomplete.v

XRdefinitions.vo : XRdefinitions.v 
	 C:\Coq\bin\coqc XRdefinitions.v

XRderiv.vo : XRderiv.v  XRbase.vo XRfunctions.vo XRlimit.vo
	 C:\Coq\bin\coqc XRderiv.v

XRfunctions.vo : XRfunctions.v  XRbase.vo XRpow_def.vo XR_Ifp.vo XRbasic_fun.vo XR_sqr.vo XSplitAbsolu.vo XSplitRmult.vo XArithProp.vo
	 C:\Coq\bin\coqc XRfunctions.v

XRIneq.vo : XRIneq.v  XRaxioms.vo XRpow_def.vo
	 C:\Coq\bin\coqc XRIneq.v

XRlimit.vo : XRlimit.v  XRbase.vo XRfunctions.vo
	 C:\Coq\bin\coqc XRlimit.v

XRList.vo : XRList.v  XRbase.vo XRfunctions.vo
	 C:\Coq\bin\coqc XRList.v

XRpow_def.vo : XRpow_def.v  XRdefinitions.vo
	 C:\Coq\bin\coqc XRpow_def.v

XRprod.vo : XRprod.v  XRbase.vo XRfunctions.vo XRseries.vo XPartSum.vo XBinomial.vo
	 C:\Coq\bin\coqc XRprod.v

XRseries.vo : XRseries.v  XRbase.vo XRfunctions.vo
	 C:\Coq\bin\coqc XRseries.v

XRsigma.vo : XRsigma.v  XRbase.vo XRfunctions.vo XRseries.vo XPartSum.vo
	 C:\Coq\bin\coqc XRsigma.v

XRsqrt_def.vo : XRsqrt_def.v  XRbase.vo XRfunctions.vo XSeqSeries.vo XRanalysis1.vo
	 C:\Coq\bin\coqc XRsqrt_def.v

XRtopology.vo : XRtopology.v  XRbase.vo XRfunctions.vo XRanalysis1.vo XRList.vo
	 C:\Coq\bin\coqc XRtopology.v

XRtrigo1.vo : XRtrigo1.v  XRbase.vo XRfunctions.vo XSeqSeries.vo XRtrigo_fun.vo XRtrigo_def.vo XRtrigo_alt.vo XCos_rel.vo XCos_plus.vo XRanalysis1.vo XRsqrt_def.vo XPSeries_reg.vo
	 C:\Coq\bin\coqc XRtrigo1.v

XRtrigo_alt.vo : XRtrigo_alt.v  XRbase.vo XRfunctions.vo XSeqSeries.vo XRtrigo_def.vo
	 C:\Coq\bin\coqc XRtrigo_alt.v

XRtrigo_def.vo : XRtrigo_def.v  XRbase.vo XRfunctions.vo XSeqSeries.vo XRtrigo_fun.vo
	 C:\Coq\bin\coqc XRtrigo_def.v

XRtrigo_fun.vo : XRtrigo_fun.v  XRbase.vo XRfunctions.vo XSeqSeries.vo
	 C:\Coq\bin\coqc XRtrigo_fun.v

XR_Ifp.vo : XR_Ifp.v  XRbase.vo
	 C:\Coq\bin\coqc XR_Ifp.v

XR_sqr.vo : XR_sqr.v  XRbase.vo XRbasic_fun.vo
	 C:\Coq\bin\coqc XR_sqr.v

XSeqProp.vo : XSeqProp.v  XRbase.vo XRfunctions.vo XRseries.vo
	 C:\Coq\bin\coqc XSeqProp.v

XSeqSeries.vo : XSeqSeries.v  XRbase.vo XRfunctions.vo XRseries.vo XSeqProp.vo XRcomplete.vo XPartSum.vo XAltSeries.vo XBinomial.vo XRsigma.vo XRprod.vo XCauchy_prod.vo XAlembert.vo
	 C:\Coq\bin\coqc XSeqSeries.v

XSplitAbsolu.vo : XSplitAbsolu.v  XRbasic_fun.vo
	 C:\Coq\bin\coqc XSplitAbsolu.v

XSplitRmult.vo : XSplitRmult.v  XRbase.vo
	 C:\Coq\bin\coqc XSplitRmult.v

