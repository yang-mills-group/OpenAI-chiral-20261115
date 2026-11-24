import YM.CF.Fixed.Fine
import YM.CF.Sedge.Pause
import YM.CF.Lattice.Anti
import YM.CF.Reflect.Reuse

/-!
CAR comparison whenever using the temporary axisCut regulator/reading on the
same (m,B) lattice. `across` is of course the same as `Spark.crossL`. Do NOT
use fiscal without transforming both readings in the reflected product. Work
with generating words in the whole sectors but it will apply to `Fixed.Probes`.
Uses also the separated layout `PositiveTest`.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 18000
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Fixed
open Function Fock NormedSpace SU Lat Lattice Cube Finset Scroll MeasureTheory Tulip Tenant Mir
open RP (E₁ E₂ rayUK slideM tiltM revX)
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology
attribute [local instance] opCStarAlgebra

-- basics relabel in d8 using `hoist`
section relabel
variable {I J : Type*}[LinearOrder I][Fintype I][LinearOrder J][Fintype J] (E:I≃J)
lemma carts_surj : Surjective (cartsL E) := by -- from d8
  have ht: Module.finrank ℂ (Wave I)=Module.finrank ℂ (Wave J):=by simp [Wave,Ket, Fintype.card_congr E]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ht (f:=(Fock.hoist E.toEmbedding ∅).toLinearMap)).mp (carts_inj _)

def across (A:FC J):FC I:= (Matrix.toEuclideanCLM (n:=Finset I) (𝕜:=ℂ)).symm ((pailL E.toEmbedding ∅).comp ((acts A).comp (Fock.hoist E.toEmbedding ∅)))
lemma carts_across (A: FC J) (p:Wave I): cartsL E (acts (across E A) p)=acts A (cartsL E p):=by
  obtain ⟨y,h⟩:= carts_surj E (acts A (cartsL E p)); unfold acts across; rw [StarAlgEquiv.apply_symm_apply]; change cartsL E (pailL _ ∅ (acts A (cartsL E p)))=_; change _=acts _ _; rw [←h]; rw [show pailL _ _ (cartsL E y)= _ from pourL E.toEmbedding ∅ (shelfG E) y]
lemma across_eq (A:FC J)(B:FC I)(s:∀ x,cartsL E (acts B x)=acts A (cartsL E x)) :across E A=B:=by apply Matrix.toEuclideanCLM.injective; apply ContinuousLinearMap.ext; intro x; apply carts_inj E; change cartsL E (acts _ _)=cartsL E (acts _ _); rw [carts_across,s]

lemma across_one : across E (1:FC J)=1:=across_eq _ _ _ fun x=> by rw [act_one,act_one]
lemma across_zero : across E (0:FC J)=0:=across_eq _ _ _ fun x=> by rw [act_zero,act_zero]; exact map_zero ..
lemma across_smul (c:ℂ)(A:FC J): across E (c•A)=c•across E A:=across_eq _ _ _ fun x=> by rw [act_smul,act_smul,carts_s,carts_across]
lemma across_add (A B:FC J) : across E (A+B)=across E A+across E B:=across_eq _ _ _ fun x=>by rw [act_add,act_add,←carts_across,←carts_across]; exact map_add (Fock.hoist E.toEmbedding ∅) _ _
lemma across_mul (A B:FC J) : across E (A*B)=across E A*across E B:=across_eq _ _ _ fun x=>by rw [act_mul,act_mul,carts_across,carts_across]
lemma across_cont : Continuous (across E) :=
  (show FC J→ₗ[ℂ]FC I from { toFun:=across E, map_add':=across_add E, map_smul':=across_smul E }).continuous_of_finiteDimensional
lemma carts_inner (X Y:Wave I): inner ℂ (cartsL E X) (cartsL E Y)=inner ℂ X Y:= sigh _ _ (shelfG E) ..
lemma across_star (A:FC J) : across E (star A)=star (across E A):=by
  apply across_eq; intro x; apply ext_inner_right ℂ; intro y; obtain ⟨z,rfl⟩:=carts_surj E y
  rw [carts_inner,act_inner,act_inner,←carts_across,carts_inner]
lemma across_put (i:I): across E (put (E i))=put i:=across_eq _ _ _ fun x=>hoist_put E.toEmbedding ∅ i x
lemma across_take (i:I): across E (takeF (E i))=takeF i:=by rw [takeF,across_star,across_put]
lemma across_sector (P: Finset J)(Q:Finset I)(t: ∀ i, E i∈P → i∈Q){b : Bool}{A}
    (h: Sector P b A): Sector Q b (across E A):=by
  induction h with
  | zero=> rw [across_zero]; apply Sector.zero
  | one=> rw [across_one]; exact Sector.one
  | up i h=> obtain ⟨x,rfl⟩:= E.surjective i; rw [across_put]; exact .up x (t x h)
  | down i h=> obtain ⟨x,rfl⟩:= E.surjective i; rw [across_take]; exact .down x (t x h)
  | add _ _ ih it=> rw [across_add]; exact ih.add it
  | mul _ _ ih it=> rw [across_mul]; exact ih.mul it
  | scale _ _ ih=> rw [across_smul]; exact ih.scale _

lemma across_quant (H: Op I) : across E (quant (portW E H))=quant H:=
  across_eq _ _ _ (fun x=> by rw [←flexL]; exact freezes E.toEmbedding ∅ (shelfG E) H x)
lemma across_twist (U:UNI I)(V:UNI J)(p:V.val= portW E U.val)(A:FC J): across E (twist (quantU V) A)=twist (quantU U) (across E A):=by
  rw [twist_formula,twist_formula,across_mul,across_mul,across_star]; change across E (quant V.val) *_*star (across E (quant V.val))=_; rw [p,across_quant]; rfl
lemma across_theta (U:UNI I)(V:UNI J)(e:V.val=portW E U.val)(A:FC J){b S}
    (h:Sector S b A): across E (theta V A)=theta U (across E A):=by
  have hp(i:I) : coat E.toEmbedding (acts U.val (basisKet i))=acts V.val (basisKet (E i)):=by
    change _= acts V.val (basisKet (E.toEmbedding i)); rw [←basis_shell,e,←flexL]; exact (origin E.toEmbedding ∅ (shelfG E) _ _).symm
  have ht(i:I) : across E (theta V (put (E i)))=theta U (across E (put (E i))):=by
    rw [across_put,theta_up,theta_up,across_smul, ←hp]; congr 1; exact across_eq _ _ _ (fun x=>hoist_r E.toEmbedding ∅ (shelfG E) _ x)
  induction h with
  | zero=> rw [theta_zero,across_zero,theta_zero]
  | one=> rw [theta_one,across_one,theta_one]
  | up i _=> obtain ⟨i,rfl⟩:= E.surjective i; exact ht i
  | down i _=> obtain ⟨i,rfl⟩:= E.surjective i; rw [takeF,theta_star,across_star,across_star,theta_star,ht]
  | add _ _ ih it=> rw [theta_add,across_add,across_add,theta_add,ih,it]
  | mul _ _ ih it=> rw [theta_mul,across_mul,across_mul,theta_mul,ih,it]
  | scale _ _ ih=> rw [theta_smul,across_smul,across_smul,theta_smul,ih]

lemma seam_theta (U V W: UNI I)(p:V.val*U.val=W.val*V.val)(A:FC I){s b}(h:Sector s b A) :
    twist (quantU V) (theta U A) = theta W (twist (quantU V) A) :=
    (by
      have he(u:Ket I) : acts V.val (acts U.val u)=acts W.val (acts V.val u):=by rw [←act_mul, ←act_mul,p]
      have ht(u:Ket I): twist (quantU V) (theta U (create u)) = theta W (twist (quantU V) (create u)):=by rw [theta_upV,twist_scalar, twist_remove, twist_create, theta_upV,he]
      induction h with
      | zero=> rw [theta_zero,map_zero,theta_zero]
      | one=> rw [theta_one,map_one,theta_one]
      | up i _=> rw [←create_put]; apply ht
      | down i _=> rw [takeF,←create_put,map_star,theta_star,theta_star,map_star,ht]
      | add _ _ ih it=> rw [theta_add,map_add,map_add,theta_add,ih,it]
      | mul _ _ ih it=> rw [theta_mul,map_mul,map_mul,theta_mul,ih,it]
      | scale _ _ ih=> rw [theta_smul,twist_scalar,twist_scalar,theta_smul,ih])
end relabel

variable {m B: Side} (i : Axis)
open RP (axisCut colony) -- tune
local notation "N_" => CSide m B
abbrev changeCut (m B: Side) (i:Axis):= fringe (anticut (CSide m B)) (axisCut m B i (anticut (CSide m B)))
local notation "U_"=> (changeCut m B i)
lemma axes_agree_reflect (x:Site (Domain m B)) : revX m B i x=(Signed.mirror i).act x:=by
  funext t; rw [RP.rev_rule]; by_cases g:i=t <;> simp [g,Signed.act, Signed.mirror]
lemma through_eq : rayUK m B i=reflConfig N_ i := by
  funext A; unfold rayUK Trip.through; simp only [Trip.torShift, Trip.paneShift, slideM, map_zero]; rfl
lemma partner_tilt (x:Site N_) : tiltM m B i x= partnerSite N_ i x:= by -- typo tweak
  apply Tenant.needle; rw [node_partner,RP.tiltR, axes_agree_reflect]

lemma fringe_zero_v (x:Site N_) : edging (anticut N_) (axisCut m B i (anticut N_)) x=
    if x∈RP.posY m B i then -1 else 1:=by
  unfold edging; rw [prod_eq_single i]; swap
  · intro l _ p; simp only [edgeF,axisCut, Function.update_of_ne p,sub_self,ZMod.val_zero]; split_ifs with h; exfalso; omega; rfl
  · simp only [edgeF, RP.posY,mem_filter,mem_univ,true_and]; change (if 0<(x i- -1).val ∧ (x i- -1).val≤(axisCut m B i (anticut N_) i- -1).val then (-1:ℂ) else 1)= _; have hp:(CSide m B).val=2*RP.oddSize m B:=RP.suff m B; have he:= RP.cval m B i (anticut N_); have hv:=ZMod.val_lt (x i); rw [sub_neg_eq_add,sub_neg_eq_add,RP.vnext,RP.vnext]; split_ifs <;> first|rfl|omega
  simp

lemma mix_seam : (U_).val * -(RP.finger m B i).val = (RP.finger m B i).val * (U_).val := by
  rw [RP.seen, ←jump_neg]; dsimp only [changeCut,fringe]; rw [jump_mul,jump_mul]; simp only [Equiv.refl_trans,Equiv.trans_refl]; congr 1; funext x
  simp only [Algebra.mul_smul_comm,Algebra.smul_mul_assoc,mul_one,one_mul,fringe_zero_v,RP.tiltSide]
  split_ifs <;> simp_all
abbrev seamFinger (m B:Side)(i:Axis): UNI (Model (CSide m B)):= ⟨-(RP.finger m B i).val,by
  apply Matrix.mem_unitaryGroup_iff.mpr; rw [star_neg, neg_mul_neg]; exact (RP.finger m B i).property.2⟩
lemma port_finger : (reflectP N_ i).val = portW (helix N_).symm (seamFinger m B i).val:=by
  rw [reflect_readout]
  rw [show Tofu (reflShape i) N_ = tiltM m B i from (Equiv.ext fun x=> (partner_tilt i x).symm), jump_neg, loveAt]; unfold unityP; rw [show (seamFinger m B i).val = -(RP.finger m B i).val from rfl,RP.seen]; rfl

def readSeam (m B:Side)(i:Axis)(A:FC (Single (CSide m B))): FC (Model (CSide m B)):= twist (quantU (changeCut m B i)) (across (helix _).symm A)
lemma seam_pos {F:Test (CSide m B)}{b:Bool}(h: InRegion (positiveRegion i) b F)(V):
    Sector (colony m B i) b (across (helix N_).symm (F V)):=by
  apply across_sector (helix _).symm _ _ _ (h.support V).sector
  intro a g; apply (RP.colony_at ..).mpr; apply (RP.holder ..).2; apply RP.north_mem .. |>.mpr -- tune syntax
  rw [mem_matterRegion] at g; exact (mem_filter.mp g).2.2.le
lemma read_sect {A:FC (Single (CSide m B))}{b}(h:Sector (colony m B i) b (across (helix N_).symm A)): Sector (colony m B i) b (readSeam m B i A) := by
  have he(F:UNI (Model N_))(W:Finset (Model N_))(e:twist F (cutM W)=cutM W){A b}(h:Sector W b A):Sector W b (twist (quantU F) A):=by
    have he(i:Model N_)(p:i∈W):Sector W true (twist (quantU F) (put i)):=by rw [←create_put,twist_create]; exact Sector.makeP _ (by nth_rw 1 [←e]; rw [←Fock.swivel,cut_basis,if_pos p])
    induction h with
    | zero => rw [map_zero]; apply Sector.zero
    | one => rw [map_one]; exact Sector.one
    | up i h=> exact he i h
    | down i h=> rw [takeF,map_star]; exact (he i h).contr
    | add _ _ ih it=> rw [map_add]; exact ih.add it
    | mul _ _ ih it=> rw [map_mul]; exact ih.mul it
    | scale _ _ ih=> rw [twist_scalar]; exact ih.scale _
  apply he _ _ _ h
  apply Mir.twist_comm
  ext x y
  rw [cutM,Matrix.mul_diagonal,Matrix.diagonal_mul]; change jump _ _ _ _ * _=_ * jump _ _ _ _; rw [jump_apply]; by_cases e : x.1=y.1
  · have ht:x∈colony m B i ↔ y∈colony m B i:=by rw [RP.colony_at,RP.colony_at,e]
    split_ifs <;> simp_all
  simp only [Equiv.refl_apply,e, ↓reduceIte,zero_mul,mul_zero]; -- tune
lemma seam_read_reflect {F:Test (CSide m B)}{b:Bool}(h: InRegion (positiveRegion i) b F)(V:Phase.Skin m B):
    readSeam m B i (reflectTest i b F V)=Reed.reverseW (RP.finger m B i) b (readSeam m B i (F (reflConfig N_ i V))) := by
  unfold readSeam reflectTest Reed.reverseW
  rw [across_smul, twist_scalar, across_theta (helix N_).symm (seamFinger m B i) _ (port_finger i) _ (h.support _).sector]; exact congrArg (Reflect.chord b • ·) (seam_theta (seamFinger m B i) U_ (RP.finger m B i) (mix_seam i) _ (seam_pos i h _))
lemma seam_read_mul (A B': FC (Single (CSide m B))) : readSeam m B i (A*B')=readSeam m B i A*readSeam m B i B':= by rw [readSeam,across_mul,map_mul]; rfl

end YM.CF.Fixed
