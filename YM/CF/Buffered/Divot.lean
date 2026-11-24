import YM.CF.Buffered.Candin
/-! Crossing & interior hops. Coordinates relative to a tile's 0. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 370000
noncomputable section
namespace YM.CF.Buffered.Region.Stripe
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Mir.Trip Phase RP MeasureTheory Roost Rails Mil RG WilsonStartup Spark Nova Fock Push.SectorMeasure Ordered
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
attribute [local instance] opCStarAlgebra
variable {m p v w B:Side}
local notation "d" => Domain v B
local notation "N" => CSide v B
local notation "S" => Locale v B

variable (i j:Axis)
def LastSite (i:Axis)(x:Post w) := x.val i = (w.val:ℤ)-1
instance (i)(x:Post w): Decidable (LastSite i x):= by unfold LastSite; infer_instance
abbrev Hale (w:Side) (i:Axis):= {x:Post w//LastSite i x}
abbrev Minor (w:Side)(i:Axis):= {x:Post w//¬LastSite i x}
def reach (x:Minor w i) : Post w:=⟨x.val.val+step i, fun j=>by
 rw [Pi.add_apply,step_apply]; split; swap; · rw [add_zero]; exact x.val.property j
 next h=> subst j; have h:= x.val.nonneg i; have v:= x.val.below i (mem_univ _); have e:x.val.val i≠(w.val:ℤ)-1:= x.property; rw [wall_mem i (mem_univ _)]; omega⟩
lemma reach_lt (x:Minor w i) : reach i x≠x.val:=fun h=> by
 have ht:(x.val.val+step i:Cover)=x.val.val:= congrArg Subtype.val h; have hq:= congr_fun ht i; rw [Pi.add_apply,step_apply,if_pos rfl] at hq; omega
-- same site in *next tile*. coordinate 0 in hop axis.
def pulse (x:Hale w i): Post w:= shades {i} x.val
lemma pulse_val (x:Hale w i): (pulse i x).val i=0:=by rw [pulse,shades_eq _ (mem_singleton_self _),wall_mem i (mem_univ _), show x.val.val i=(w.val:ℤ)-1 from x.property,sub_self]
lemma shades_reach (x:Minor w i) (p:i ≠ j): (shades {j} (reach i x)).val= (shades {j} x.val).val+step i:=by
 funext l; by_cases h:l=j; swap; · rw [shades_other _ (mem_singleton.not.mpr h), Pi.add_apply,shades_other _ (mem_singleton.not.mpr h)]; rfl
 subst l; rw [shades_eq _ (mem_singleton_self _),Pi.add_apply,shades_eq _ (mem_singleton_self _),step_apply,if_neg (Ne.symm p),add_zero]
 simp [reach,step_apply,Ne.symm p]
lemma shades_return (x:Minor w i) : (shades {i} x.val).val= (shades {i} (reach i x)).val + step i:=by
 funext l; unfold reach shades; simp only [Pi.add_apply,step_apply,mem_singleton]; split_ifs <;> omega
lemma Waist (i j:Axis){A:Finset Axis}(x:Roost w A) : shades {i} (shades {j} x)=shades {j} (shades {i} x) := by
 apply Subtype.ext; funext l; unfold shades; simp only [mem_singleton]; split_ifs <;> omega
lemma reflected_in (i j:Axis)(x:Post w)(p:i≠j) : LastSite i (shades {j} x) ↔ LastSite i x:= by unfold LastSite; rw [shades_other _ (mem_singleton.not.mpr p)]

def acrossMinor (p:i≠j) : Equiv.Perm (Minor w i) := (mirrorR {j}).subtypeEquiv (fun x=> (reflected_in i j x p).not.symm)
def alongTail (x:Minor w i):Minor w i:=⟨shades {i} (reach i x),fun h=> by
 change (shades _ _).val _= _ at h; rw [shades_eq _ (mem_singleton_self _),wall_mem i (mem_univ _)] at h
 change (w.val:ℤ)-1-(x.val.val i+(step i:Cover) i)=_ at h; simp only [step_apply,if_true] at h; have he:= x.val.nonneg i; omega⟩
lemma sendAlong (x:Minor w i): reach i (alongTail i x)=shades {i} x.val:= Subtype.ext (shades_return i x).symm
lemma along_sq (x:Minor w i): alongTail i (alongTail i x)=x:=Subtype.ext (by change shades {i} (reach i (alongTail i x))=_; rw [sendAlong,shades_square])
def flipAlong (i:Axis): Equiv.Perm (Minor w i) := ⟨alongTail i,alongTail i, along_sq i, along_sq i⟩
def acrossHale (p:i≠j) : Equiv.Perm (Hale w i):=(mirrorR {j}).subtypeEquiv (fun x=>(reflected_in i j x p).symm)

-- gauge terminal transport, orientation
abbrev Hitch (i:Axis)(w:Side):=Roost w {i}
-- from tail/into head. Can use same for inner hops also
abbrev exitF (v B: Side)(x: Post (CSide v B)): Hitch i (Domain v B) := ofpost {i} (upstairs v B x)
def entryF (v B:Side)(x:Post (CSide v B)): Hitch i (Domain v B):=⟨(exitF i v B x).val-step i,fun k=>by
 have he:= (exitF i v B x).property k; change 0 ≤ _ ∧ _≤_ at he; rw [Pi.sub_apply,step_apply]; split; swap; · rw [sub_zero]; exact he
 next h=> subst k; have ht:0<(exitF i v B x).val i:= up_strict ..; omega⟩
lemma exit_to (x:Post N): shades {i} (exitF i v B x)=entryF i v B (shades {i} x):=by
 apply Subtype.ext; apply eq_sub_of_add_eq; rw [←show flipC _ {i} (upstairs v B x).val=(shades {i} (exitF i v B x)).val+step i from (flip_edge {i} i (exitF i v B x)).trans (by rw [if_pos (mem_singleton_self i)]), up_turn]; rfl
lemma entry_from (x:Post N): shades {i} (entryF i v B x)=exitF i v B (shades {i} x):=by nth_rw 1 [←shades_square x {i}]; rw [←exit_to,shades_square]
lemma exit_arc (x:Post N)(p:i≠j): shades {j} (exitF i v B x)=exitF i v B (shades {j} x):=Subtype.ext (((flip_edge {j} i (exitF i v B x)).trans (by rw [if_neg (mem_singleton.not.mpr p),add_zero])).symm.trans (up_turn ..))
lemma entry_arc (x:Post N)(p:i≠j): shades {j} (entryF i v B x)=entryF i v B (shades {j} x):= by nth_rw 1 [←shades_square x {i}]; rw [←exit_to, Waist, exit_arc i j (shades {i} x) p, Waist j, exit_to,shades_square]

def outWay (i:Axis)(x:Post N)(a:S): E:= a.1 i (exitF i v B x)
def inWay (i:Axis)(x:Post N)(a:S): E:=a.1 i (entryF i v B x)
lemma way_x (x:Post N)(a: Locale v B): outWay i x (past {i} a)= (inWay i (shades {i} x) a)⁻¹:=by
 unfold outWay past inWay; simp [exit_to]
lemma way_i (x:Post N)(a: Locale v B): inWay i x (past {i} a)= (outWay i (shades {i} x) a)⁻¹:=by
 unfold outWay past inWay; simp [entry_from]
lemma way_t (x:Post N)(a: Locale v B)(p:i≠j): outWay i x (past {j} a) = outWay i (shades {j} x) a:=by unfold outWay past; simp [p,exit_arc i j _ p]
lemma way_o (x:Post N)(a: Locale v B)(p:i≠j): inWay i x (past {j} a) = inWay i (shades {j} x) a:=by unfold inWay past; simp [p,entry_arc i j _ p]
lemma way_cont (x:Post N): Continuous (inWay (v:=v) (B:=B) i x) ∧ Continuous (outWay (v:=v) (B:=B) i x):=by constructor <;> first|(unfold outWay; fun_prop)|(unfold inWay; fun_prop)

local notation "δt" => Uniform p
instance {δ:Axis→Side}(t:Rail δ)(i:Axis): Decidable (endsAt t i):= by unfold endsAt; infer_instance
def chordF {δ:Axis→Side}(r:Rail δ)(i:Axis):ℝ:= if endsAt r i then -1 else 1
variable (K:Ordered m v p) (B)(r:Rail (Uniform p))
local notation "k" => spirit K B
local notation "y" => sugar K B
lemma minor_to (x:Minor N i): Planck.zone k r x.val.val+step i=Planck.zone k r (reach i x).val:=by rw [show (reach i x).val=x.val.val+step i from rfl,Planck.zone_add, wrap_step]
lemma hale_to (x:Hale N i): Planck.zone k r x.val.val+step i=Planck.zone k (Region.next i r) (pulse i x).val:=by
 rw [Planck.next_zone]; rw [←wrap_step (CSide m B),← Planck.zone_add]; apply congrArg; funext j; simp only [Pi.add_apply,pulse,shades,mem_singleton, Pi.smul_apply]; by_cases h:j=i; swap; · simp [h,step_apply]
 subst j; rw [if_pos rfl,step_apply,if_pos rfl,wall_mem i (mem_univ _),show x.val.val i=((CSide v B).val:ℤ)-1 from x.property, nsmul_eq_mul]; omega
lemma windsAt (x:Post N): Planck.zone k r x.val i= -1 ↔ LastSite i x ∧ endsAt r i:=by
 have he:= Planck.pilot k r x i; unfold LastSite endsAt
 let n:=CSide m B; have hv: 1< n.val:= suff_pos m B
 have hk:(r i).val < p.val:=(r i).isLt; have ha: (x.val i).toNat< (CSide v B).val:=by have h':= x.nonneg i; have hx:= x.below i (mem_univ _); omega
 rw [← (ZMod.val_injective n.val).eq_iff,he]; -- tune
 have hs: (-1:Per n).val+1=n.val:= by
    letI : Fact (1 < n.val) := ⟨hv⟩; rw [ZMod.val_neg_of_ne_zero, ← (show ((1:ℕ):Per n) = 1 from Nat.cast_one), ZMod.val_natCast_of_lt hv]; omega -- tune
 change _ = (-1:Per n).val ↔ _; have hx:= (K.spirit B).ratio; change n.val=(CSide v B).val*p.val at hx; have hc:= x.nonneg i; constructor
 · intro w; have hp:(r i).val+1=p.val:=by nlinarith
   refine ⟨?_,hp⟩; have hh: (x.val i).toNat+1=(CSide v B).val:=by rw [←hp,Nat.mul_add,Nat.mul_one] at hx; omega
   omega
 intro h; have hv: (r i).val+1=p.val:=h.2; obtain ⟨u,t⟩:=h; have hh:(x.val i).toNat+1=(CSide v B).val:=by omega
 rw [← hv, Nat.mul_add, Nat.mul_one] at hx; omega
lemma walks (r':Rail (Uniform p))(x z:Post N)(h:Planck.zone k r x.val+step i=Planck.zone k r' z.val)(F:Pack m B):
 links F.1 (Planck.zone k r x.val,i)= outWay i x (reel r (K.fromCube F))*inWay i z (reel r' (K.fromCube F)):=by
 unfold links outWay inWay; rw [butter,butter]; dsimp only; have hh:= after (Planck.zone k r x.val) i; rw [h, up_sends (K:=K),up_sends (K:=K)] at hh
 rw [up_sends (K:=K)]; change _=_; rw [show (entryF i v B z).val = _ from (show (entryF i v B z).val=(upstairs v B z).val-step i from rfl), placeMinus (K:=K), hh, add_sub_cancel_right]; rfl -- tune
end YM.CF.Buffered.Region.Stripe
#print axioms YM.CF.Buffered.Region.Stripe.walks
