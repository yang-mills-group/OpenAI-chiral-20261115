import YM.SU5.LitCurrent.Forest
import YM.CF.Prism.Gale
-- Cut the very assigned kernels to a trace sector. Preserves all Suite costs.
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 450000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.LitCurrent
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
-- true for tens. accept all on none for joint pricing
namespace Chamber
abbrev Division := Finset ℕ
variable {N:Side} (P:Division) (Y:Pane N) (G:Seat N→ SU.E) (o:Site N)
    {a b d:ℝ} {V:Openc (More N) d}
local notation "I" => Single N
abbrev existsSlot(P:Division)(u:SU.Slot) := SU.charge u ∈ P
def fortune(P:Division)(N:Side):Finset (Single N):= univ.filter fun i=> existsSlot P i.2
abbrev markG (P:Division)(N:Side):Op (Single N):=cutM (fortune P N)
local notation "Ξ" => markG P N
local notation "z'" => SU.z
local notation "Z" => tradew N fun _=>central
variable (i j:I) {x:Op (Single N)} (s:Sa N)
local notation "V∇" => fortune P N
lemma atRight (i j:I) (X:Op I) : (X * Ξ) i j= if j ∈ V∇ then X i j else 0:=by rw [markG,cutM,Matrix.mul_diagonal]; split_ifs<;>simp
lemma atLeft (i j:I) (X:Op I) : (Ξ*X) i j= if i∈ V∇ then X i j else 0:=by rw [markG,cutM,Matrix.diagonal_mul]; split_ifs<;>simp
lemma runsNear (X:Op I)(h:∀ i j,X i j≠0→ (i∈ V∇↔j∈ V∇)) : Commute Ξ X:=by
 unfold Commute SemiconjBy; ext i j
 rw [atLeft,atRight]; by_cases y:X i j=0; simp [y]; exact if_congr (h i j y) rfl rfl
lemma stamp_charge : (Z).val=Matrix.diagonal fun i=> z'^(SU.charge i.2):=by
 ext ⟨x,u⟩ ⟨y,v⟩; by_cases h:x=y<;> simp [h,tradew,jump_apply,show triple (fund central)=Matrix.diagonal _ from by_charge,Matrix.diagonal_apply]
lemma seal_star : star Ξ=Ξ:= (cutM_idp _).isSelfAdjoint
lemma seal_sq : Ξ * Ξ=Ξ:= (cutM_idp _).isIdempotentElem
lemma seal_cc : cc Ξ=Ξ:=by ext a b; by_cases u:a=b<;>simp [u, markG,cutM,apply_ite star]
-- equality of charge detected faithfully. no broken-sym hypothesis.
lemma toCharge {i j:SU.Slot} (h:z'^(SU.charge i)=z'^(SU.charge j)) : SU.charge i= SU.charge j:=by
 have hb(i:SU.Slot) : SU.charge i < 5:=by rcases i with ⟨_,_|_⟩ <;> simp [SU.charge]
 exact SU.z_prim.pow_inj (hb i) (hb j) h -- tune
lemma channelStay (u:SU.E)(i j:SU.Slot)(h:(matter u).val i j≠0): SU.charge i=SU.charge j:=by
 apply toCharge; have ht:=congrArg (fun x:UNI SU.Slot=>x.val i j) (show matter central*matter u=matter u*matter central from by rw [←map_mul,←map_mul,central_ok]); change ((matter central).val*(matter u).val) i j=((matter u).val*(matter central).val) i j at ht; rw [by_charge,Matrix.diagonal_mul, Matrix.mul_diagonal,mul_comm ((matter u).val i j)] at ht; exact mul_right_cancel₀ h ht
lemma postMark (G:Seat N→ SU.E): Commute Ξ (tradew N G).val:=by
 apply runsNear; rintro ⟨x,i⟩ ⟨y,j⟩ p; unfold tradew at p; simp only [jump_apply,Equiv.refl_apply] at p; split at p; next t=> simp only [fortune,existsSlot,mem_filter,mem_univ,true_and]; rw [channelStay _ _ _ p]
 contradiction
lemma seated (p: Commute (Z).val x): Commute Ξ x:=by
 apply runsNear; intro i j w; have u:=congrArg (fun t:Op I=> t i j) p.eq; simp only [stamp_charge (N:=N),Matrix.diagonal_mul, Matrix.mul_diagonal] at u; rw [mul_comm (x i j)] at u
 simp only [fortune,existsSlot,mem_filter,mem_univ,true_and]; rw [toCharge (mul_right_cancel₀ w u)]
lemma situated {F:Openc (More N) d → Op I} (p:Inter (bail N d) (bail N d) F) (X:Openc (More N) d)(v:X.val=profile Y): Commute Ξ (F X):=by
 let u:=fun _:Seat N=> central; have he:Lattice.gauge u Y=Y:=funext fun i=>show central*Y i*central⁻¹=_ from by rw [central_ok,mul_inv_cancel_right]
 have hv:(forum N d).drive u X=X:= by apply Subtype.ext; change relayg u X.val=X.val; rw [v,←profile_g,he]
 have h:=p u X; rw [hv] at h; exact seated _ (show Commute _ _ from h.symm)
lemma sits {F:SOp N}(p: Solo a b F d) (z:profile Y∈Openc (More N) d): Commute Ξ (F (profile Y)):=by
 obtain ⟨H,W,h,_,v⟩:=p; rw [show F (profile Y)= _ from v ⟨profile Y,z⟩]; apply Commute.sum_right; intro i _; exact situated P Y (h i).frame _ rfl
-- operations on permanent supports; retain prices exactly, even on larger length reservations inherited.
noncomputable abbrev hall (X:Op (Single N)):Op (Single N):= markG P _ * X * markG P _
lemma hallAt (X:Op I)(i j:I) : hall P X i j=if i∈ V∇ ∧ j∈ V∇ then X i j else 0:=by rw [hall,atRight,atLeft]; split_ifs <;> first|rfl|tauto
lemma hallFlat (x:Op I)(u:Commute Ξ x): hall P x= Ξ * x:=by unfold hall; rw [←u.symm.eq,mul_assoc,seal_sq,u.symm.eq]; -- orientation check
lemma suite {F:Openc (More N) d → Op I}{S:Sa N}{V:Toll I} (p:Suite (badge _) (bail N d) (bail N d) S V F) : Suite (badge _) (bail N d) (bail N d) S V (fun x=>hall P (F x)):=by
 refine ⟨⟨fun i z=>?_,fun i j=>?_⟩,License.times _ (License.times (g:=F) _ (License.base _ Ξ) p.fuel) (License.base _ Ξ)⟩
 · unfold hall; let R:= (bail N d).run i; have he: Ξ*R.val=R.val*Ξ:= (postMark P i).eq; have hv:=p.frame i z; change _*R.val=R.val*_ at hv; calc
     Ξ * _ * Ξ * R.val = R.val * Ξ * F z * Ξ:=by rw [mul_assoc,show Ξ*R.val=R.val*Ξ from he,←mul_assoc,mul_assoc Ξ,hv,←mul_assoc,he]
     _ = _:= by unfold R; simp only [mul_assoc]
 · simp_rw [hallAt]; by_cases u:i∈ V∇ ∧ j∈ V∇
   · simp_rw [if_pos u]; exact p.expo i j
   simp_rw [if_neg u]; exact ⟨(p.expo i j).positive,(p.expo i j).triggered,fun _=> by rw [norm_zero]; exact (p.expo i j).positive,fun x y=> by simp only [sub_self,norm_zero]; exact mul_nonneg ((p.expo i j).positive) ((forum N d).pos _ _ _), continuous_const⟩
lemma soak {F:SOp N} (p: Soak (node o) F a b d): Soak (node o) (fun x=> hall P (F x)) a b d:=by
 obtain ⟨F,W,h,z,e,t⟩:=p; exact ⟨_,_,fun i=>suite P (h i),z,e,fun i=> by dsimp only; rw [t i,hall, Finset.mul_sum, Finset.sum_mul]⟩
-- sweep motion. One SU.Slot
variable (t:Sweep N)
lemma travel : ech t Ξ=Ξ:=by
 unfold ech; rw [singT,show windX t.charge Ξ= Ξ from (by cases t.charge; rfl; exact seal_cc ..)]; apply Mir.twist_comm; symm; apply runsNear -- tune symm goal eq uses another direction
 rintro ⟨⟨x,i⟩,h⟩ ⟨⟨y,j⟩,g⟩ b'; let A:=castX t; let U:= spinU t.charge t.s; have hak:h=g:=by
    change jump (Tofu A N) (fun i=>(milU A U (xtra t.charge) i).val) (x,(i,h)) (y,(j,g)) ≠ 0 at b'; rw [jump_apply] at b'; split at b'; next v=> by_contra e; apply b'; change (A.payA x) • (U.val i j*(1:Op SU.Slot) h g)=0; rw [Matrix.one_apply_ne e,mul_zero,smul_zero]
    contradiction
 subst g; simp [fortune]
lemma travelR (b:Bool)(x:Op I): realR t b (hall P x)= hall P (realR t b x):=by
 let tA(y:Op I):=ech t y; have h:tA (hall P x)=markG P N * (tA x)*markG P N:=by unfold hall tA; rw [echo_mult,echo_mult,travel]
 cases b <;> cases e:detX t.s<;> first|exact h|simp only [realR,Bool.false_eq_true,↓reduceIte,Sour.bolt,foeL,hitL,doveL,Thera.jazz,e]; first|exact h|change -star (tA _)= Ξ * (-star (tA _)) * _; rw [h,star_mul,star_mul,seal_star,mul_neg,neg_mul,mul_assoc]|change star (tA _)= Ξ * star (tA _) * _; rw [h,star_mul,star_mul,seal_star,mul_assoc]
end Chamber
end YM.CF.LitCurrent
