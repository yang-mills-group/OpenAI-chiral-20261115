import GaugeFieldConstruction.NauticalStampNX
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3200
set_option linter.unusedSectionVars false
set_option maxHeartbeats 100000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
namespace Spine
open Aria Set OS.Semigroup Ballad Six Glaze
open Papal FrameP Fock.Flux YM.Gleam BProof.PricePort Gleam.Guide Gleam.clocks
open Lead Designs XGarden XGarden.MastTin XGarden.MastTin.ArtCart
variable (P:Spine){n:ℕ}
def ErlangNX (j:Axis)(T:Finset Cover)(C:ℝ)(s:ℕ) : Prop:=∃ w:ℕ,∃ (σ:Cover)(D:Finset Cover)(m:ℤ), T⊆D ∧ 0<w ∧ SlabMark.Etch.House P.calibration w σ 0 (plow P.calibration j m D)∧σ j=0∧ (SlabMark.Etch.ratio P.calibration.B w:ℝ) ≤ C
lemma evergreenNX (S:Finset Cover)(j:Axis): ∃ C:ℝ,∀ s:ℕ,P.ErlangNX j S C s:=by
   obtain ⟨k,hk⟩:∃ k:ℕ,S⊆ cartO 0 k:=by
      have h:∀ᶠ k:ℕ in atTop,∀ x∈S,x∈cartO 0 k:= by
         refine (eventually_all_finset S).mpr (fun x _=>?_); filter_upwards [eventually_all.mpr (fun i:Axis=>eventually_ge_atTop ((x-(0:Cover)) i).natAbs)] with a u; exact (cart_spec ..).2 u
      exact h.exists.imp (fun k p _ q=>p _ q)
   let u:=k+P.calibration.ℓ +1; let w:=2*u; let m:ℤ:=u; let σ(i:Axis):ℤ:=if i=j then 0 else -m; refine ⟨_,fun s=>⟨w,σ,_,m,hk,Nat.mul_pos (by decide) (Nat.succ_pos _),?_,by simp [σ],le_rfl⟩⟩
   unfold w; push_cast; exact Heritor.mastHaus P k j
variable {Q: Py.Rate.LocalLimit.Badge}{t:ℕ}{u:TintDemand}(H: LicensedHeight (tagged_B Q) t u P.par)
include H
lemma evergreenOneNX (j:Axis)(cost:ℕ→P.Test→ℂ)(R:Porch P cost j)(X:BeaconNX n):Tendsto (fun s=>cost s (P.plaqueStakeNX X)) atTop (𝓝 (quoteP_NX X κF)):=by
 obtain ⟨C,v⟩:=P.evergreenNX X.1.patio j
 have ht: Tendsto (fun s=> (2:ℝ)*ClockTurn (P.urnMark s)) atTop (𝓝 0):=by
    simpa only [Function.comp_apply,mul_zero] using (((show RunRate (-callE/16) 0 ClockTurn from RunRate.coins ..).tends (Or.inl (by norm_num [callE,gratuity]))).comp (turnover P.par)|>.const_mul (2:ℝ))
 apply tendsto_iff_norm_sub_tendsto_zero.mpr
 refine squeeze_zero' (Eventually.of_forall fun s=>norm_nonneg _) ?_ ht
 filter_upwards [P.confirmCallNX n 1 Q t u H (fun _=>C) (RunRate.const _)] with s p
 obtain ⟨w,V,S,m,hX,pos,hu,z,g⟩:=v s
 have he:X.1.patio ⊆ S:=hX
 have hx:=p [X] w V S j m (by simp) (fun i h=>List.mem_singleton.mp h|> fun e=> e.symm ▸ he) pos hu z g cost R (quoteP_NX X κF) (P.sampleOneNX ..)
 rw [sharePageNX,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] at hx; exact hx
lemma RealityBlendNX (N:ℕ)(Z:Lead.Clan):star (quoteP_NX (P.PillNX N Z) κF)= quoteP_NX (P.PillNX N Z) κF:=by
 let X:=P.PillNX N Z; let Y:= P.flash N; let J:=P.plaqueStakeNX X; let B:=flipBeaconNX X 3 0
 have he:B=((Y.mirror 3 0),NarcNX Z,(0:Fin 2),(0:Fin 2)):=rfl -- shuffle?
 have hu:quoteP_NX B κF= quoteP_NX X κF:= by rw [he]; exact (polarityAccNX Z _ rfl).trans (polarityAccNX Z _ rfl).symm
 have hz : P.reflectTest 3 J= P.plaqueStakeNX B:= (P.gestureNX X _).trans (by rw [show rotorCostNX 3 _ _ = 1 from (bkNX_paid 3 0).trans (if_pos rfl),one_smul])
 have ht:= P.evergreenOneNX H 3 _ (P.publicH 3) X; have hx:= P.evergreenOneNX H 3 _ (P.publicH 3) B
 refine (tendsto_nhds_unique (ht.star.congr fun i=> (?_: star (P.publicBill i J)=P.publicBill i (P.plaqueStakeNX B))) hx).trans hu
 rw [←hz]; exact (P.EraH 3 0 i _).symm
abbrev cFlatstockNX (N:ℕ)(Z:Lead.Clan) := numeralNX N*quoteP_NX (P.PillNX N Z) κF
lemma stockRealNX (N:ℕ)(Z:Lead.Clan) : star (P.cFlatstockNX N Z) = P.cFlatstockNX N Z:=by unfold cFlatstockNX; rw [star_mul,P.RealityBlendNX H]; simp [numeralNX,mul_comm,Complex.star_def]
variable (Z:Lead.Clan){M:P.Menagerie}{a:ℝ}{x:P.Spectrum0 3}(h:P.Company n M a)
omit h
lemma stockPayNX (x:P.Spectrum0 3): Tendsto (fun i:ℕ=>P.singleState 3 i x (P.frontMat Z n)) atTop (𝓝 (P.cFlatstockNX n Z)):=by
 have hp:= (P.evergreenOneNX H 3 _ (P.privateH x 3) (P.PillNX n Z)).const_mul (numeralNX n)
 exact hp.congr fun i=>by rw [purchaseStampNX,map_smul]; rfl
include h
lemma companyEarnNX (x:P.Spectrum0 3): P.electro M Z=P.cFlatstockNX n Z:=by
 let c:ℂ:= ↑(purePrice Z); have hp:c≠0:= by unfold c; exact_mod_cast (purePrice_p Z).ne'
 have hv:P.frontMat Z n=c • P.defaultR Z n:=by unfold defaultR; rw[smul_smul,mul_inv_cancel₀ hp,one_smul]; rfl
 have hz: P.Taste (P.defaultR Z n) (P.flash n).patio (M Z).y:=by
   have he:= (M Z).worth; rw[h.clock Z] at he; exact he
 have ht:= (Taste.sticker x (P.defaultBay Z n) (P.defaultColor Z n) hz).const_mul c
 have hQ : Tendsto (fun s:ℕ=> P.singleState 3 s x (P.frontMat Z n)) atTop (𝓝 (P.electro M Z)):=by
    rw [hv,electro,mul_comm]; exact ht.congr fun i=> (map_smul ..).symm -- tune
 exact tendsto_nhds_unique hQ (P.stockPayNX H Z x)
#print axioms stockRealNX
#print axioms companyEarnNX
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
