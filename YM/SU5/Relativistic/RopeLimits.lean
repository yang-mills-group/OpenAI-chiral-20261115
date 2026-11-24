import YM.SU5.Relativistic.Rope
set_option autoImplicit false
set_option synthInstance.maxSize 25000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
namespace FermionSlab
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat PhaseChoice SlabMark Vacancy Tapestry Tapestry.Altitude Tapestry.Exhibition Tower.Selected
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {a b:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H a b I E)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{i k:ℕ→ℕ}(Q:Coherent Y H (i:=a) (k:=b) (E:=E) D i k)
variable (u:ℕ→ℕ)(T:ℕ→ Bool→Family (tent Y H)→Family (tent Y H))(t:GradesAll (i:=a) (a:=i) (k:=b) (b:=k) Y H u T)
local notation "W"=> wingspan Λ l


variable (s n:ℕ)(X:ℕ→ Finset Cover)
local notation "A" r:max=> a (i (u r))
local notation "B" r:max=> b (k (u r))
namespace Lariat
section dominated
variable {K':Calibration}
-- exact footprint sequence for budget (can handle all finite recs). Coordinates given per participating height.
def Costs (X:ℕ→Finset Cover) : {n:ℕ}→ Lariat K' n→ Prop
 | _, start f=> f.S=X 0
 | n+1,stretch f g=> Costs X f∧ g.S=X (n+1) -- X binding check

def runningBox (Λ:Preparation)(l:ℕ)(X:ℕ→Finset Cover) : ℕ→ Finset Cover
 | 0=> X 0
 | n+1=> wingspan Λ l (runningBox Λ l X n) ∪ X (n+1)
lemma hires {f:Lariat K' n} (q: Costs X f): box Λ l f=runningBox Λ l X n:=by induction f with| start f=>exact q| @stretch n f g ih=> change wingspan _ _ _∪g.S=wingspan _ _ _ ∪_; rw [ih q.1,q.2]
lemma boards (f:Lariat K' n):∃ S, Costs S f:=by
 induction f with
 | start f=> exact ⟨fun _=>f.S,rfl⟩
 | @stretch k f g ih=>
    obtain ⟨S,e⟩:=ih; let H(i:ℕ):= if i≤ k then S i else g.S; exact ⟨H, agrees f e (fun i q=> (if_pos q).symm), (if_neg (by omega)).symm⟩
where
 agrees {n:ℕ}{K'':Calibration}{S T:ℕ→ Finset Cover}(f:Lariat K'' n)(p:Costs S f)(t:∀ i:ℕ,i≤ n→ S i=T i):Costs T f:=by
           induction f with| start f=> exact Eq.trans p (t 0 le_rfl)| @stretch n f g ih=> exact ⟨ih p.1 (fun i v=> t _ (v.trans (by omega))),Eq.trans p.2 (t _ le_rfl)⟩
end dominated

local notation "E₀" f:max=> rideL Y H T s f
local notation "U" m:max f:max=> priceAt Y H s (A m) (B m) f
open FermionSlab
include V Q t
set_option maxHeartbeats 600000 in
lemma cashLine (C':ℝ)(p:0<C'):∃ c:ℝ,0<c∧ ∀ e:ℝ,0<e→∀ᶠ m:ℕ in atTop,∀ f:Lariat (tent Y H) n,f.Costs X→ priced (fun _=> C') f →pay (E₀ f) c∧pay (U m f) c∧pay ((U m f) - E₀ f) e:=by
 induction n with
 | zero=>
    refine ⟨C',p,fun e p=> Eventually.of_forall fun i f g h=>?_⟩
    cases f with| start f=> exact ⟨h,h, show pay (f.mark-f.mark) e from by rw [sub_self]; intro i x; simp [p.le]⟩
 | succ n ih=>
    obtain ⟨r,w,pn⟩:=ih
    let A₀:= runningBox Λ l X n
    let c(b):= (t.links A₀ (s+n) b).choose; have hc(q):= (t.links A₀ (s+n) q).choose_spec
    let K₀:= max (c true) (c false); have hk:0<K₀:= lt_max_of_lt_left (hc true).pos; have hp(v): c v≤K₀:= by cases v <;> first| exact le_max_right ..| exact le_max_left ..
    let ν:= K₀*r*C'
    have hg:0<ν:=by unfold ν; positivity
    refine ⟨ν,hg,?_⟩; intro e v
    let δ:= e/C'; have hd:0<δ:= div_pos v p
    let t1:= δ/2/K₀; have ht:0<t1:= by positivity
    let t2:= δ/2/r; have ht':0<t2:= by positivity
    filter_upwards [pn _ ht, (eventually_all (ι:=Bool)).2 fun i=> (hc i).converges _ ht'] with m pz Kx f j Uc
    cases f with
    | stretch f g=>
       have Ut:InTest K true A₀ (hue f) (E₀ f):= (show box Λ l f=A₀ from hires n X j.1) ▸ aboard Y H u T t s f
       have Gm:InTest K true A₀ (hue f) (U m f):= (show box Λ l f=A₀ from hires n X j.1) ▸ groundPrice Y H s f _ _ -- order
       obtain ⟨hz,gq,e0⟩:= pz f j.1 Uc.1
       let B₁:=moveUp Y H (s+n) (A m) (B m) A₀ (hue f)
       let Y₀:= T (s+n) (hue f)
       let R:=(E₀ f); let R':=(U m f)
       have hh : pay (Y₀ R) (K₀*r):=fun i x=>( (hc (hue f)).bdd _ Ut r hz i x).trans (mul_le_mul_of_nonneg_right (hp _) w.le)
       obtain ⟨hx,hu'⟩:= Kx (hue f) (U m f) Gm r gq
       have hP : pay (B₁ R') (K₀*r):= fun i x=>(hx i x).trans (mul_le_mul_of_nonneg_right (hp _) w.le)
       change pay (Y₀ R*g.mark) ν ∧ pay (moveUp Y H (s+n) (A m) (B m) (box Λ l f) (hue f) R' * g.mark) ν ∧ pay ((U m (stretch f g))-Y₀ R*g.mark) e
       rw [hires n X (f:=f) j.1]
       refine ⟨pay_mul hh (show pay g.mark C' from Uc.2), pay_mul hP (show pay g.mark C' from Uc.2),?_⟩
       rw [priceAt,hires n X (f:=f) j.1]
       change pay (B₁ R'*g.mark-Y₀ R*g.mark) e
       have he: Y₀ R' - Y₀ R=Y₀ (R'-R):=by
          rw [sub_eq_add_neg R',show Y₀ (R'+ -R)=_ from t.addL Y H V Q u (s+n) Gm (inNeg Ut), ←neg_one_smul ℂ R]
          rw [show T (s+n) f.hue ((-1:ℂ) • R)= (-1:ℂ) • Y₀ R from t.scaleL Y H V Q u (s+n) Ut (-1)] -- rw both R on lhs?
          rw [neg_one_smul]; exact sub_eq_add_neg _ _
       have hE: pay (B₁ R'-Y₀ R) δ:= by
          intro i x; simp_rw [Pi.sub_apply]
          refine (norm_sub_le_norm_sub_add_norm_sub _ (Y₀ R' i x) _).trans ?_
          have hN: ‖Y₀ R' i x-Y₀ R i x‖ ≤ K₀*t1:= by
             change ‖(Y₀ R'-Y₀ R) _ x‖≤_
             rw [he]; exact ((hc _).bdd _ (inLess Gm Ut) t1 e0 i x).trans (mul_le_mul_of_nonneg_right (hp _) ht.le)
          apply (add_le_add (hu' i x) hN).trans_eq -- note hu bound `t2*r` not hx
          rw [show t2*r=δ/2 from div_mul_cancel₀ _ w.ne',mul_comm K₀, show t1*K₀=δ/2 from div_mul_cancel₀ _ hk.ne']; ring
       rw [← _root_.sub_mul, show e=δ*C' from (div_mul_cancel₀ e p.ne').symm]; exact pay_mul hE (show pay g.mark C' from Uc.2)
end Lariat

end FermionSlab
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
