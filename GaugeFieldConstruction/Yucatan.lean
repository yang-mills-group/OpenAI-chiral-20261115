import GaugeFieldConstruction.Pontchart
set_option autoImplicit false
set_option maxHeartbeats 50000
noncomputable section
namespace YM.GaugeFieldConstruction.Wick.Yacht
open StressFHeat MeasureTheory Analysis Function Filter Metric Maxwell Finset Gap Complex Cauchy Row Phys Flux.One Lamp Conj
open Lattice CF CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart CF.XGarden.MastTin.ArtCart.Violets CF.Py.Rate.LocalLimit.Papal
open scoped Topology ContDiff BigOperators Classical
open HopeC CF.Buffered CF.Buffered.Lifted FlightFlux Fluxim TableF
-- Gem data extracted via basis coordinate
namespace Vesper
variable (x:GIndex)
def E_G: Gem:= by
 let q(i j):= ((F i j) x).re
 refine ⟨q,fun i j=>?_⟩; unfold q; nth_rw 1 [U1.Gauge97.turnover i j]; simp
lemma realisticG (i j:Axis): tr GIndex (F i j)=F i j:=by
 rcases lt_trichotomy i j with h|h|h
 · exact realistic ⟨(i,j),h⟩ -- tune
 · rw [h,U1.Gauge97.zero_angle,map_zero]
 rw [U1.Gauge97.turnover i j,map_neg]; congr 1; exact realistic ⟨(j,i),h⟩
lemma RealT (z:ℂ)(p:bar z=z):Complex.ofReal z.re=z:=by
 refine Complex.ext (z:= (z.re:ℂ)) rfl ?_; exact (Complex.conj_eq_iff_im.mp p).symm -- tune
lemma portal (i j): (F i j) x=(E_G x|>.val i j:ℂ):= (RealT ((F i j) x) (congrArg (fun i:GJet=> i x) (realisticG ..))).symm
lemma cycG (i j k:Axis): Gder i (F j k)+Gder j (F k i)+Gder k (F i j)=0:= by
 apply loyalty; intro a; rw [LinearMap.mem_ker]; let w:= a.1.val.face a.2; have ht(i j): w.read (F i j)=w.skin i j:=by rw [Maxwell.read_F]; simp [power,Maxwell.skin]
 have he (p i j): w.read (Gder p (F i j))= w.p p*w.skin i j:=by rw [← LinearMap.comp_apply, w.frequency, LinearMap.smul_apply,ht]; rfl
 change w.read _=0; rw [map_add,map_add,he,he,he]; exact w.rigor.closed ..
def E_D: Sut:= by
 let h(i j k:Axis):= (Gder i (F j k) x).re; refine ⟨h,⟨fun i j k=>?_,fun i j k=>?_⟩⟩
 · unfold h; nth_rw 1 [U1.Gauge97.turnover]; simp
 have hp:=(congrArg (fun u:GJet=>(u x).re) (cycG i j k)); simpa only [Finsupp.add_apply,add_re,Finsupp.zero_apply,zero_re] using hp -- tune
lemma portion (i j k): (Gder i (F j k)) x=(E_D x|>.val i j k:ℂ):=by
 have ht: tr GIndex ((Gder i) (F j k))=Gder i (F j k):=by
    have hp:= LinearMap.congr_fun (Gmoves i) (F j k); simpa only [LinearMap.comp_apply, realisticG] using hp
 exact (RealT (Gder i (F j k) x) (congrArg (fun u:GJet=> u x) ht)).symm
-- mean of W1 shifts
abbrev meanH (H:HopeC E4)(p:Axis):ℝ:=∫ x,x p ∂H.μ
lemma mean_P (H G:HopeC E4)(p): meanH (addQ H G) p=meanH H p+meanH G p:=by
 let f(x:E4):=x p; have h:Continuous f:=by unfold f; fun_prop
 unfold meanH; rw [add_l (h:= h.continuousOn)]; change (∫ x,(∫ y,f x+f y ∂G.μ) ∂H.μ)=_
 simp_rw [integral_add (f:=fun _=>_) (integrable_const _) (span_c G h), integral_const, measureReal_univ_eq_one,one_smul]; rw [integral_add (span_c H h) (integrable_const _)]; simp [f] -- tune
lemma mean_T (x:E4)(p):meanH (point x) p=x p:=integral_dirac ..
lemma wire_K (i j):meanH (Rodς i) j=0:=by
 let r:ℝ:=2⁻¹; unfold Rodς meanH; rw [rolled (v:=(show Continuous (fun x:E4=> x j) from by fun_prop).continuousOn)]; change (∫ t in Set.Ioc (-r) r,t*basis i j) =0; rw [integral_mul_const]; suffices (∫ t in Set.Ioc (-r) r,t) =0 by rw [this,zero_mul]
 rw [← intervalIntegral.integral_of_le (by unfold r; norm_num: -r≤ r),integral_id]; ring -- tune
lemma specZero (k): meanH SpecW k=0:=by
 have h:meanH CubeW k=0:=by unfold CubeW; rw [mean_P,mean_P,mean_P]; simp only [wire_K]; ring -- bug chaining
 unfold SpecW; rw [mean_P,mean_P,h]; ring
open Wilson
-- Coordinates.G.Glint ext. seam uses canonical
lemma star_Y (i:Wα)(x:Cover)(p:Axis): meanH (Glint x i) p= lineP (i.1-x) i.2.1.val.1 i.2.1.val.2 p:=by
 let H:=addQ (Foliants i.2.1) SpecW; let f:= billMark (off x) (off i.1) 1; let τ:ℝ:=2⁻¹; have ht: (∫ u,f u p∂H.μ)=off i.1 p+ meanH H p-off x p:=by
    have he(x:E4):Continuous (fun u:E4=> u p):=by fun_prop
    unfold f billMark meanH; simp_rw [one_smul]
    change (∫ u, ((off i.1) p+u p)-(off x) p∂H.μ)=_; rw [integral_sub (show Integrable (fun u:E4=> (off i.1 p)+u p) H.μ from (span_c H (by fun_prop))) (integrable_const _), integral_add (integrable_const _) (span_c H (he 0))]; simp
 have hu:meanH (Glint x i) p=off i.1 p+meanH H p-off x p:=(rolled H f (by unfold f billMark; fun_prop) (fun u:E4=>u p) (v:=(show Continuous (fun u:E4=>u p) from by fun_prop).continuousOn)).trans ht
 rw [hu,show meanH H p=_ from mean_P ..,specZero, add_zero]
 unfold Foliants Larch; rw [mean_P,mean_P,mean_P]; simp [mean_T, wire_K,lineP,digit,hit]; split_ifs<;>ring -- tune
end Vesper
end YM.GaugeFieldConstruction.Wick.Yacht
end
