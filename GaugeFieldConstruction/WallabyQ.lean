import GaugeFieldConstruction.AndrosJ
import GaugeFieldConstruction.BootHearthJ
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4200
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock
namespace WallsQ
variable (d:Side)
local notation "Ζ" => ZMod (2*d.val)
local notation "ℤu" =>Axis→ZMod (2*d.val)
abbrev dialQ (d:Side):=Axis→ZMod (2*d.val)
local notation "ρ"=> dialQ d
local instance (d:Side): NeZero (2*d.val):=⟨(mul_pos (by decide) d.property).ne'⟩
def posQ (d:Side)(j:Axis)(v:ℤ)(x:dialQ d) : Prop:= (x j - (v:ZMod (2*d.val))).val < d.val
def bendQ (d:Side)(j:Axis)(v:ℤ)(x:dialQ d):dialQ d:= fun i=> if i=j then (2:ZMod (2*d.val))*v-x i-1 else x i
variable (v:ℤ) (j:Axis)(x:dialQ d)
@[simp] lemma bend_here: bendQ d j v x j =(2:Ζ)*v-x j-1:= by simp [bendQ]
lemma bend_there {k:Axis}(h:k≠j): bendQ d j v x k=x k:=by simp [bendQ,h]
lemma bend_in (s:ℤ): Involutive (bendQ d j s):=by intro y; funext k; unfold bendQ; split_ifs <;> abel
local notation "t₀"=> d.val
lemma ajNorm (n:ℕ)(w:n < 2*d.val): ((n:Ζ)).val=n:=ZMod.val_natCast_of_lt w
lemma overtuneQ : (↑(d.val):Ζ)+(d.val)=0:=by
 rw [←Nat.cast_add,← two_mul, ZMod.natCast_self]
variable {d}
private lemma conjugate_beadQ (n:ℕ)(h:n<2*d.val): (-(↑n:Ζ)-1).val=2*d.val-n-1:=by
 have h1:n+1 ≤ 2*d.val:=by omega
 let t:= 2*d.val-n-1
 have hc:t+n+1=2*d.val:=by unfold t; omega
 have he:(↑(2*d.val):Ζ)=0:=ZMod.natCast_self _
 have hp: (t:Ζ)+(n:Ζ)+1=0:=by rw [←Nat.cast_add,←Nat.cast_one (R:=Ζ),←Nat.cast_add,hc,he]
 rw [show -(n:Ζ)-1=(t:Ζ) from by linear_combination -hp]
 exact ajNorm _ t (by unfold t; omega)
lemma bead_posQ {y:Ζ}(h:y.val<d.val) : (y - ↑(d.val):Ζ).val=y.val+d.val:=by
 trans ((↑(y.val+d.val):Ζ)).val
 · rw [Nat.cast_add,ZMod.natCast_zmod_val]
   rw [sub_eq_add_neg, neg_eq_iff_add_eq_zero.mpr ?_] -- tune
   exact overtuneQ _
 rw[ZMod.val_natCast_of_lt (by omega)]
lemma bead_negQ {y:Ζ}(h:d.val ≤ y.val): (y - ↑(d.val):Ζ).val=y.val-d.val:=by
 have ht:=ZMod.val_lt y
 change y.val<2*d.val at ht
 rw[show y-(d.val)=(↑(y.val-d.val):Ζ) from (by rw[Nat.cast_sub h,ZMod.natCast_zmod_val]),ZMod.val_natCast_of_lt (by omega)]
variable (d)
lemma pos_refQ: posQ d j v (bendQ d j v x) ↔ ¬posQ d j v x:=by
 unfold posQ; rw[bend_here]
 let V:=x j - (v:Ζ); have ht:=ZMod.val_lt V; have h:=conjugate_beadQ V.val ht
 rw [ZMod.natCast_zmod_val] at h
 rw[show (2:Ζ)*↑v-x j-1-↑v=-V-1 from by unfold V; ring,h]; change 2*d.val-V.val-1 < d.val ↔ ¬ V.val <d.val -- tune
 omega
lemma pos_backQ: posQ d j (v+d.val) x ↔ ¬posQ d j v x:=by
 let z:= x j-(v:Ζ); unfold posQ; push_cast; rw [show x j-((v:Ζ)+(d.val))=z-↑(d.val) from by unfold z; ring]
 change (z- (↑(d.val):Ζ)).val < d.val ↔ ¬z.val < d.val
 by_cases e:z.val<d.val
 · rw [bead_posQ e]; omega
 rw [bead_negQ (by omega)]; have ht:=ZMod.val_lt z; omega
lemma rev_backQ: bendQ d j (v+d.val)=bendQ d j v:=by
 funext x i; unfold bendQ; split <;> push_cast <;> try rfl
 have h:=overtuneQ d; linear_combination h
variable {d} {C:Type}[Fintype C][Nonempty C]
-- Max data propagation for mosaic.
def reflectQ (d:Side)(j:Axis)(v:ℤ)(x:dialQ d→C) :dialQ d→C:=fun y=> if posQ d j v y then x y else x (bendQ d j v y)
-- Move walls. v ranges all, allows negative case v+d.
structure Melon (d:Side)(M:(dialQ d→C)→Prop):Prop where
 move :∀ c:dialQ d→C, M c→∀ j:Axis,∀ v:ℤ, M (reflectQ d j v c)
local notation "Zen" S:max X:max => (∀ (x y:dialQ d),(∀ i:Axis, i∉ S→x i=y i) → X x=X y)
-- Rip.Text.Condition: all across j-range v..v+n−1
lemma move2Q {j:Axis}{S:Finset Axis}{X:ρ→C}(h:j ∉ S)(p:∀ (x y:dialQ d),(∀ i:Axis, i∉ S→x i=y i) → X x=X y)(v:ℤ):Zen S (reflectQ d j v X):=by
 intro x y p'; unfold reflectQ posQ; rw[p' j h]; split; exact p _ _ p'; exact p _ _ fun i e=> by unfold bendQ; rw [p' i e]
-- rank along one cyclic window represented by reference row function Z across x ignoring j.
def flatQ (d:Side)(X:dialQ d→C)(j:Axis)(v:ℤ)(Z:dialQ d→C)(l:ℕ):Prop:=∀ x, (x j - (v:ZMod (2*d.val))).val < l → X x= Z x
-- Z independent
local notation "iM" d:max t:max=> (dialQ d→ t)
-- positive half extension backward
lemma glowQ (j:Axis){X Z:dialQ d→C}{v:ℤ}{k:ℕ}(p:flatQ d X j v Z k)(u:Zen ({j}:Finset Axis) Z)(h: k≤ d.val): flatQ d (reflectQ d j v X) j (v-k:ℤ) Z (k+k):=by
 intro x b; unfold reflectQ; let a:= (x j-(v:Ζ)); change _
 rw [Int.cast_sub,show x j - (_-_) = a+(k:Ζ) from by push_cast; unfold a; ring] at b
 have H: k+k ≤ 2*d.val :=by omega
 have ht:=(a+(k:Ζ)).val_lt; let y:=(a+(k:Ζ)).val; change y<k+k at b
 have hy:a=(y:Ζ)-(k:Ζ):=by unfold y; rw [ZMod.natCast_zmod_val]; ring
 by_cases e:k ≤ y
 · have hN:y-k<k:=by omega
   have hw:y-k <2*d.val:=by omega
   have hr:a.val=y-k:= by rw [hy, ← Nat.cast_sub e,ajNorm _ _ hw] -- `hy` dependent
   rw [if_pos]; exact p x (by change a.val<k; omega)
   unfold posQ; change a.val<_; omega
 have hx:y<k:=by omega
 have hk:k-y-1< k:=by omega
 have hg:k-y-1 <d.val := hk.trans_le h
 have ha:(bendQ d j v x j- ↑v:Ζ)= ↑(k-y-1):=by
    rw[bend_here,show (2:Ζ)*v-x j-1-↑v= - a-1 from by unfold a; ring,hy,Nat.cast_sub (by omega:1≤ k-y),Nat.cast_sub (by omega:y ≤ k)]; push_cast; ring
 have he:(bendQ d j v x j-(v:Ζ)).val=k-y-1:=by rw [ha,ZMod.val_natCast_of_lt (by omega)]
 rw[if_neg, p (bendQ d j v x) (by omega)]; exact u _ _ fun i hi=> bend_there _ _ _ _ (by simpa using hi)
 exact (pos_refQ d v j x).mp (show posQ d j v (bendQ d j v x) from by unfold posQ; omega)
lemma LargeWallQ {S:Finset Axis}{M:(dialQ d→C)→Prop}(i:Axis)(z:i∉ S)(h:Melon d M) {k:ℕ}(e:k ≤ d.val)(pT:0< k){x0:dialQ d→ C}(hv:Zen ({i}:Finset Axis) x0) (X:dialQ d→C)(v:ℤ)(u:M X)(w:Zen S X)(p: flatQ d X i v x0 k): ∃ X:dialQ d→C, M X∧ X=x0 ∧∀ (x y:dialQ d),(∀ j:Axis, j∉ S→x j=y j) → X x=X y:=by
 induction e using Nat.decreasingInduction generalizing v X with
 | self=>
   let Y:=reflectQ d i v X; refine ⟨Y,h.move X u i v,?_,move2Q z w v⟩; funext x; apply glowQ i p hv le_rfl x; rw[← two_mul]; exact ZMod.val_lt _
 | of_succ n g ih=>
   refine ih (by omega) _ (v-n:ℤ) (h.move X u i v) (move2Q z w v) fun y a=> glowQ i p hv (by omega) y ?_; omega
lemma stickerQ {S:Finset Axis}{M:(dialQ d→C)→Prop}(h:Melon d M)(X:dialQ d→C)(u:M X): ∃ x:dialQ d→C,M x ∧∀ (a b:dialQ d),(∀ j:Axis,j∉ S→ a j=b j) → x a=x b:=by
 induction S using Finset.induction_on with
 | empty=> exact ⟨X,u,fun x y q=>by rw [funext (f:=x) (g:=y) (fun i=>q i (notMem_empty _))]⟩
 | @insert i s a ih=>
   obtain ⟨x,p,q⟩:=ih; let Y:=fun r:dialQ d=>x (fun j=>if i=j then 0 else r j); have ht:flatQ d x i 0 Y 1:=by
     intro a b; unfold Y; have h': a i=0:=by simpa [ZMod.val_eq_zero] using (show (a i - ((0:ℤ):Ζ)).val=0 by omega)
     refine congrArg x ?_; funext k; split; next U=> subst k; exact h'
     rfl
   have hu (p y:dialQ d)(h:∀ k:Axis,k∉ ({i}:Finset Axis)→ p k=y k):Y p=Y y:=by
     refine congrArg x ?_; funext k; split_ifs with b; rfl; exact h k (by simpa using Ne.symm b)
   obtain ⟨F,f,hf,U⟩:=LargeWallQ (S:=s) i a h (show 1≤d.val from d.property) (by simp) hu x 0 p q ht
   refine ⟨F,f,?_⟩; rw [hf]; intro v w g; unfold Y; apply q; intro c hc; split_ifs with H; · rfl
   exact g c (by simp [Ne.symm H,hc])
lemma sheetQ {M:(dialQ d→C)→Prop}(h:Melon d M)(X:dialQ d→C)(u:M X): ∃ c:C, M (fun _=>c):=by
 obtain ⟨Y,H,t⟩:=stickerQ (S:=univ) h X u
 refine ⟨Y 0,?_⟩; rwa [show (fun _=>Y (0:dialQ d))= Y from funext fun y=> t _ _ (by simp)]
#print axioms sheetQ
#print axioms rev_backQ
end WallsQ
end YM.CF.Buffered.Afterglow.Tower.SlabMark
end
