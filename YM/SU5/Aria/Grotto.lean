import YM.SU5.Aria.Contessa
import YM.SU5.Cheer.Harp
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Set
open Cheer (Narrow)
variable (P:Spine)(x:P.Spectrum0 3)(Z:Lead.Clan)(s n:ℕ)
local notation "K"=> P.calibration
local notation "Λ"=> P.par
local notation "R"=> ruler P.par.block
local notation "H"=> P.ColorHil 3 (P.advocate 3 x 3)
local notation "Ω"=> P.heaven 3 (P.advocate 3 x 3)
local notation "ω"=> P.colorZero 3 (P.advocate 3 x 3)
local notation "S"=> P.seasons 3 (P.advocate 3 x 3)
local notation "π"=> P.advocate 3 x 3
local notation "G"=> P.ManyF 3 π
local notation "V"=>P.shifts 3
local notation "p"=> P.stockS Z (P.flash n)
local notation "ℓ"=> P.calibration.ℓ
local notation "u"=> (P.flash n).patio
local notation "Ξ"=> P.viewF 3 π s
abbrev fascinated (D:P.Apron):Prop:= D.s=s∧ V (D.u 3:ℤ) D.F=(P.stockS Z (P.flash n))∧ D.S=plow K 3 (-(D.u 3:ℤ)) u ∧ ∀ i: Trans (3:Axis), D.u i.val = (ℓ)+1
lemma bulletWidth : ∀ᶠ m:ℕ in atTop, Between K 3 0 (R*((m:ℤ)+m)) u:=by
 have hp:=P.flash_here n; have hc:∀ i∈ u,∀ᶠ m:ℕ in atTop,(ℓ:ℤ) + i (3:Axis)≤ R*((m:ℤ)+m):=by
    intro i _; let y:ℤ:= (ℓ:ℤ)+i 3; filter_upwards [eventually_ge_atTop y.toNat] with m h; have hh:(m:ℤ)+(m:ℤ) ≤ R*(m+m:ℤ):= le_mul_of_one_le_left (by positivity) (ruler_gene _); change y≤ _; omega
 filter_upwards [ (u).eventually_all|>.mpr hc] with m t i h; exact ⟨hp i h,(by simpa [add_comm] using t i h)⟩
lemma fascination :∃ D:P.Apron, P.fascinated Z s n D:=by
 obtain ⟨k,h,t⟩:= ((P.bulletWidth n).and (eventually_gt_atTop 0)).exists; let h₀:= plow K 3 (-(k:ℤ)) u; let A:= V (-(k:ℤ)) p; let B:= Function.update (fun _ : Axis=> ℓ+1) 3 k
 have hb: Between K 3 (- R*(k:ℤ)) (R*(k:ℤ)) h₀:=by
   have he:= h.relocate K 3 (-(k:ℤ)); rw [show ruler (K).B=R from rfl,mul_neg, add_zero,_root_.mul_add, ← add_assoc,neg_add_cancel,zero_add] at he; simpa [neg_mul] using he
 have hc:B (3:Axis)=k:=update_self ..; have he (i:Axis)(v:i≠3):B i=ℓ+1:= Function.update_of_ne v ..
 have hx:p∈enclave K:=P.celebrity (flourish _ _)
 have hr(i:Axis): Between K i (-R*(B i:ℤ)) (R*(B i:ℤ)) h₀:=by
    by_cases v:i=3; · subst i; rw [hc]; exact hb
    intro a w; obtain ⟨a,b,rfl⟩:=plow_stays K 3 (-(k:ℤ)) u w; rw [SlabMark.moves,if_neg v,P.flash_fixed i n a b v]; have h:((ℓ+1:ℕ):ℤ) ≤ R*((ℓ+1:ℕ):ℤ):= le_mul_of_one_le_left (by positivity) (ruler_gene _); rw [neg_mul,he i v]; omega
 let D:P.Apron:=⟨s,B,(fun i=>by
   by_cases h:i=(3:Axis); · simpa only [h,hc]
   rw [he i h]; omega),A,h₀,P.shifts_support 3 _ _ (P.visibility Z n),P.shifts_keep _ _ hx,hr⟩
 refine ⟨D,rfl,?_,?_,fun i=>he _ i.property⟩
 · change V (B 3:ℤ) _ = _; rw [hc]; change V (k:ℤ) A=(P.stockS Z (P.flash n)); unfold A; rw [P.shifts_sum,add_neg_cancel,P.shifts_zero]
 change _=plow K 3 (-(B 3:ℤ)) u; rw [hc]
noncomputable def crownT : P.Apron:= (P.fascination Z s n).choose
local notation "F"=> P.crownT Z s n
lemma ordained:P.fascinated Z s n F:= (P.fascination Z s n).choose_spec
lemma practices (D:P.Apron)(f:P.Test)(a:P.shifts 3 (D.u 3:ℤ) D.F=f)(b:D.s=s)(g:P.birthF 3 s f): D.engine P 3 π ω=P.viewF 3 π s g:= by
 subst s; rw [P.engine_view]; exact P.identical_F 3 π _ _ _ ((D.card_price P 3).trans a)
lemma seeding : (F).engine P 3 π ω= P.shard x Z s n:= P.practices x s _ _ (P.ordained Z s n).2.1 (P.ordained Z s n).1 (P.brightC Z s n)
lemma template: P.defaultR Z n=(purePrice Z:ℂ)⁻¹ • (P.shifts 3 ((F).u 3:ℤ) (F).F):= by rw [(P.ordained Z s n).2.1]; rfl
abbrev MarginX := 3*(P.calibration.ℓ+1)
local notation "D₀"=> P.MarginX
abbrev markX := whenly (timeMesh P.par) s 1
noncomputable def leftX : P.Model0:= P.announce 3 F (P.markX s)
noncomputable def following : Cover:= fun i=> if i=(3:Axis) then 0 else P.MarginX -- r ∈ Γ^4
abbrev palp : Vantage:= P.laysM (P.vtile s P.following)
noncomputable def rightX : P.Model0:= ((P.crownT Z s n),(P.leftX Z s n).2+P.palp s)
local notation "L₀"=> P.leftX Z s n
local notation "L₁"=> P.rightX Z s n
lemma book_height : 0<P.markX s:=when_pos _ _ _ zero_lt_one
lemma roll_time : P.palp s (3:Axis)=0:= by unfold palp laysM vtile following; simp [notch,bell]
lemma rightFare : P.rayFare 3 L₁=(P.markX s:ℝ):=by
 change (L₀).2 3+P.palp s (3:Axis)-_= _; rw [P.roll_time,add_zero]; exact P.timeFare ..
lemma singleCrew : [L₀]∈P.Crest0 3∩P.roll0 3 ∧ [L₁]∈P.Crest0 3∩P.roll0 3:=⟨P.mayEnter 3 F (P.markX s) (P.book_height s), P.loneCrest 3 _ _ (P.book_height s) (P.rightFare ..)⟩
local notation "η"=> P.joinHeight 3 [L₀] [L₁]
local notation "Σ₀"=> Prod.fst (α:=P.Apron) (β:=Vantage)
local notation "Σ₁"=> Prod.snd (α:=P.Apron) (β:=Vantage)
lemma order_here (i:Axis) : P.Turnstile i Σ₀ η Σ₁:=by
 by_cases h:i=(3:Axis); · subst i; exact P.concat_toRank 3 (P.singleCrew Z s n).1.2 (P.singleCrew Z s n).1.1 (P.singleCrew Z s n).2.2 (P.singleCrew Z s n).2.1
 let y:=P.turnModel 3 L₀; have he:y.2 i= (L₀).2 i:= by apply if_neg h; -- defeq?
 have hp:(L₀).2 i=0:= Pi.single_eq_of_ne h _
 let a:= ℓ+1; let t:=bell (timeMesh Λ) s; have hx: t ((a+a:ℕ):ℤ)< t (P.MarginX:ℤ):=by
    apply lt_of_not_ge; intro w; have hw:= (bell_le (timeMesh Λ) s ..).1 w; unfold a MarginX at *; omega
 change List.Pairwise (fun a b:P.Model0=> P.resignY i _ _ a < P.porchY i _ _ b) [y,L₁]; rw [List.pairwise_pair]; change (y.2 i)+(F).realWidth P i< ((L₀).2 i+P.palp s i)-(F).realWidth P i; rw [he,hp,zero_add, zero_add, show P.palp s i=t D₀ from (by change t (P.following i)=_; unfold following; rw [if_neg h]), show (F).realWidth P i=t (a:ℤ) from ?_]; swap; · unfold Apron.realWidth; rw [(P.ordained Z s n).1,(P.ordained Z s n).2.2.2 ⟨i,h⟩] -- field
 rw [lt_sub_iff_add_lt]; rw [show t (a:ℤ)+t (a:ℤ)=t ((a+a:ℕ):ℤ) from ?_]; exact hx
 rw [Nat.cast_add a a]; exact (bell_add (timeMesh Λ) s a a).symm
lemma onGrid : ∃ v:P.Model0→ Lattice.Cover, ∀ i∈ P.joinHeight 3 [L₀] [L₁], P.laysM (P.vtile s (v i))=i.2:=by
 classical
 let a:= (F).u 3; let b: Cover:=Pi.single (3:Axis) ((a:ℤ)+1); let X':= (L₀).2; let ξ:= P.vtile s; let T:=timeMesh Λ; let c(i:Cover):=P.laysM (ξ i); let y:=P.turnModel 3 L₀
 have hf:c b=X':=by
    funext i; change bell T s (b i)= Pi.single (M:=fun _:Axis=>ℝ) (3:Axis) ((F).realWidth P 3+(P.markX s:ℝ)) i; by_cases h:i=3; · subst i; rw [show b 3=(a:ℤ)+1 from Pi.single_eq_same .., Pi.single_eq_same,bell_add,show (F).realWidth P 3=bell T s a from (by unfold Apron.realWidth; rw [(P.ordained Z s n).1]),show (1:ℤ)= (1:ℕ) from rfl]; try exact congrArg _ (natural_time T s 1)
    simp [b,h, bell]
 have hd:c (-b)=y.2:=by
    have hu:c (-b)= - c b:=by funext i; change bell T s (-(b i))=_; simp [bell]; rfl
    rw [hu,hf]; funext i; dsimp only [y,turnModel]; unfold mirrorΩ; split_ifs with v; · subst i; rfl
    change -(aislePt 3 _ i)=aislePt 3 _ i; simp [aislePt,v]
 have hw: c (b+P.following)=(L₁).2:=by
    change c _= X'+P.palp s; rw [←hf]; exact funext fun i=>bell_add ..
 have hp: ∀ i∈η, ∃ r:Cover,c r=i.2:=by intro i t; rcases (show i=y ∨ i=L₁ from (by simpa [joinHeight,y] using t)) with rfl|rfl; exact ⟨-b,hd⟩; exact ⟨_,hw⟩ -- `rfl` substitutes y?
 choose! f v using hp; exact ⟨f,v⟩
abbrev pairStory:= joinHeight P 3 [P.leftX Z s n] [P.rightX Z s n]
/-- frame-level comparison with SAME χ and rigid coordinates, ANY matching assignment accepted (mark family `f`'s frames do not grow across periods afterward). No mathematical claim about the value averaging across frames. -/
lemma clearSight (i:Axis)(J:P.Ellis 3 x)(r:P.Model0→ Lattice.Cover)(h:∀ b∈(P.pairStory Z s n),P.laysM (P.vtile s (r b))=b.2):
 P.commonWell 3 x Σ₀ Σ₁ (P.pairStory Z s n)=P.singleState i s (P.advocate 3 x i) (P.fullScroll s Σ₀ r (P.pairStory Z s n)):=by
 let d:=η; let Y':=(F); let x':= P.advocate 3 x i; let Q:= P.vtile s ∘ r
 let R':= P.laysM ∘ Q; have hh: P.Plenum Σ₀ d R':=⟨fun k=> ⟨d,List.Perm.refl _, P.turn_lists_fax _ _ _ _ _ (fun i k=>(h i k).symm) (P.order_here Z s n k)⟩⟩
 have hv:P.Turnstile i Σ₀ d Σ₁:= P.order_here ..; have hg: P.Turnstile i Σ₀ d R':= P.turn_lists_fax _ _ _ _ _ (fun i k=>(h i k).symm) hv
 refine (P.common_cult 3 x _ _ _ J (List.Perm.refl d) hv).trans ?_
 have hc : P.memorial i x' Σ₀ d R'= P.memorial i x' Σ₀ d Σ₁:= receive_list_fax _ d (P.seasons i x') _ _ _ _ _ _ _ (fun i t=>by unfold porchY resignY commuteTight; change ((_) ∧ _); rw [show R' i=Σ₁ i from h i t]; exact ⟨rfl,rfl,rfl⟩) -- tune
 refine hc.symm.trans ((P.entirely_now 3 x _ _ J i Q hg hh).symm.trans (P.turn_purchase i x' Σ₀ r s d hg ?_)); intro v f; rcases (show v=P.turnModel 3 L₀ ∨ v=L₁ from (by unfold d joinHeight at f; simpa using f)) with eq|eq <;> subst v <;> exact (P.ordained Z s n).1.le -- Simpa!
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.clearSight
