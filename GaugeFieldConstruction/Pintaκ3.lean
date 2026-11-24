import GaugeFieldConstruction.MoskaP3
import GaugeFieldConstruction.Sommar
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 100000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry Grotto
namespace Ivey
open Sault Leaf Sour
open Ladder3 Drapes Tenant Palot Rue Iona
attribute [local instance] loreM loreN
variable {n: Side}{I α β γ G:Type}[LinearOrder I][Fintype I][Fintype α][Fintype β][Fintype γ]
-- old bank
namespace ShoreQ
open Tuner
variable (P:BudgetPoint)
namespace Argos
open Rio Iona Isle Py
variable {n:Side}{I γ M D:Type}[LinearOrder I][Fintype I][Fintype M][Fintype γ]
section
variable (P:BudgetPoint)(σ:I→Seat n)(F:KK I (Copy n) n)(W0:Finset I→Pax n)(Q0:Finset I→ Cusp n)(Q:LeaseQ γ n)(L:ℕ)(C:I→M→Factor3 n)(S:Ids n)(Y:Orbit n)
variable (o:Seat n)(i:I) (R l:List I)
local notation "Φ"=> Book3 P σ F W0 Q0 Q L C S
local notation "H"=> penStep P σ F W0 Q0 Q L C S
structure StarL (N:Rio I n):Prop where
    topP (i:PI I n): pureX N i≠0 → i.1∈realm_C σ
    topB (i:KI I n): N.B i ≠0 → i.1∈realm_C σ
-- forgot σ in header auto? syntax check
lemma pureAdd3 (A B:Rio I n): pureX (A+B)=pureX A+pureX B:=by change A.X+B.X+(A.Y+B.Y)= A.X+A.Y+(B.X+B.Y); abel
lemma stern_R (l:List I): StarL (σ:=σ) (Book3 P σ F W0 Q0 Q L C S l):=by
    have hΦ{U A T: Type}[Fintype T][DecidableEq U][AddCommGroup A](v:T→ dues I U→ A)(j:dues I U)(u:j.1∉realm_C σ)(p:∀ i,v i j=0):(∑ i:T,v i) j=0:=by rw [Finset.sum_apply]; exact sum_eq_zero fun i _=>p i
    have he{A U:Type}[AddCommGroup A][DecidableEq U](x:dues I U)(t:x.1∉ realm_C σ)(L:List I)(p:U)(c:A):clipK σ p L c x=0:=by
       unfold clipK; refine if_neg (fun p=>?_) ; exact t ((congrArg Prod.fst p.2) ▸ (show L.toFinset∈ realm_C σ from mem_filter.mpr ⟨mem_univ _,pays_z σ p.1⟩)) -- cast direction depends h:p.1 ... x=(...)
    induction l using List.reverseRecOn with
    | nil=> exact ⟨fun i h=>False.elim (h (zero_add _)),fun i v=>False.elim (v rfl)⟩ -- tune
    | append_singleton l i ih=>
       rw [Book3_cons]; refine ⟨fun j p=>Classical.byContradiction (fun s=>p ?_),fun j p=>Classical.byContradiction (fun s=>p ?_)⟩
       · rw[pureAdd3,Pi.add_apply,show (pureX (Φ l)) j=0 from Classical.byContradiction (fun h=>s (ih.topP j h)),zero_add]; unfold penStep purchase3; rw [κpClip]; apply hΦ _ _ s; intro b; unfold Rinc; apply hΦ _ _ s; intro u; apply he _ s
       change (Φ l).B j+(H _ _).B j=0; rw[show (Φ l).B j=0 from Classical.byContradiction (fun h=>s (ih.topB j h)),zero_add]; unfold penStep purchase3 Rio.payment; dsimp only; unfold fullY; apply hΦ _ _ s; intro i; unfold Kinc; apply hΦ _ _ s; intro q; apply hΦ _ _ s; intro y; apply he _ s
-- push growth.Account elementary.Herm progress per θ.
def ΛLine (y:Key I)(X:Rio I n) : Support (More n) → Vox3 n→ Cipher n:= DropW Y (WritV σ W0 y) (WritV σ Q0 y) (Canz σ _ (pureX X) y)
def ReefB (y:Key I)(X:Rio I n) : Force n→ Cipher n:= fun i=> Canz σ _ (F+X.B) y i Y
local notation "Δ"=> ΛLine σ W0 Q0 Y
local notation "A"=> ReefB σ F Y
variable (y:Key I) (t:∀ i∈l, σ i=o)
include t
lemma laneOn : ∀ (x:Key I), let z:= blank3 σ o x
 ΛLine σ W0 Q0 Y z (Book3 P σ F W0 Q0 Q L C S (R++l))= ΛLine σ W0 Q0 Y z (Book3 P σ F W0 Q0 Q L C S R) ∧ ReefB σ F Y z (Book3 P σ F W0 Q0 Q L C S (R++l))=ReefB σ F Y z (Book3 P σ F W0 Q0 Q L C S R):=by
 induction l using List.reverseRecOn with
 | nil=> simp
 | append_singleton l i ih=>
    intro x W; obtain ⟨v,s⟩:= ih (fun i p=>t i (List.mem_append_left _ p)) x; rw[← List.append_assoc,Book3_cons]; refine ⟨Eq.trans ?_ v, Eq.trans ?_ s⟩ -- infer W vs suffix
    all_goals have h:W i=0:=by unfold W blank3; rw [if_pos (t i (by simp))]
    all_goals let N:=Φ (R++l); let X:= H N i; have κ:= pennyOff3 Q (Frame3 σ W0 Q0 N) (FortX3 F N) i σ W S (C i) (Platform Q (C i) P L) h -- tune
    · unfold ΛLine; rw[pureAdd3]; apply congrArg; funext i; rw [puff_add]; rw[show Canz σ _ (X.pureX) W =0 from κ.1]; exact add_zero _ -- tune X defEq rw
    funext p; unfold ReefB; rw [show F+(N+X).B=(F+N.B)+X.B from (add_assoc ..).symm,puff_add]; change Canz σ _ (F+ N.B) W p Y+Canz σ _ X.B W p Y=_; rw[show Canz σ _ X.B W= _ from κ.2]; exact add_zero _
section
local notation "FCN"=> FC (Dwell n)
variable {J:Type}[Fintype J][LinearOrder J](a:Seat n→ J)(h:Injective a)(x:Key I)(b:Bool)(G: FC (Dwell n)→+ FC (Dwell n))(p:∀ s:ℂ,∀ y:FC (Dwell n),G (s • y)=ρ3 b s • G y)
-- Word ordering linears. list ordered.Phy.
def rite3 (V:Support (More n)→Vox3 n→ Cipher n)(z:Hub n):FC (Dwell n):=(l.map (fun i=> x i • PortJ Q VoxSpace (C i) (Platform Q (C i) P L) Y V z)).sum
abbrev rime3 (V:Support (More n)→Vox3 n→Cipher n)(F0:Force n→ Cipher n)(i:Force n):FC (Dwell n):= (l.map (fun j=> x j • FrontJ Q VoxSpace (C j) (Platform Q (C j) P L) Y V F0 i)).sum
local notation "Mκ"=> Reflect3 σ a b x
local notation "Vζ" s:max=>blank3 σ o (Mκ s)
local notation "Pψ" s:max Y:max=> ΛLine σ W0 Q0 Y (blank3 σ o (Reflect3 σ a b x s)) (Φ R)
variable (U:∀ j∈l,∀ i:M,∀ D:Support (More n), Fock.Sector univ false ((C j i).issue D Y))(w:∀ j∈l,∀ i:M,∀ k,(C j i).issue ∅ (Y.1,k)=(C j i).issue ∅ Y)(d:∀ i j,Q.issue i ∅ (Y.1,j)=Q.issue i ∅ Y)(v:∀ i∈realm_C σ,Bake.Turf (W0 i))
variable (T:∀ i:KI I n,F i≠0→ i.1∈realm_C σ)
include h p U w d v t
set_option maxHeartbeats 270000 in
lemma StrideW (z:Hub n): Kin (id:J→J) (fun i=>ag_top G Y.1 (Canz σ _ (pureX (Book3 P σ F W0 Q0 Q L C S (R++l))) (Reflect3 σ a b x i) z)) (fun s=>ag_top G Y.1 (Canz σ _ (pureX (Book3 P σ F W0 Q0 Q L C S R)) (Reflect3 σ a b x s) z)+G (rite3 P Q L C Y l (Reflect3 σ a b x s) (ΛLine σ W0 Q0 Y (blank3 σ o (Reflect3 σ a b x s)) (Book3 P σ F W0 Q0 Q L C S R)) z)):= by
 induction l using List.reverseRecOn with
 | nil=>
    simp only [List.append_nil, rite3, List.map_nil,List.sum_nil,map_zero, add_zero]; exact Kin.refl id (Connect.Hatch.rivers id _ (canH σ a h x b (axle_P G Y.1) (ax_s b G Y.1 p) z _)) -- Type. p
 | append_singleton l i ih=>
    let X:= Φ R; let V:=Φ (R++l); let e(s:Key J):= Vζ s; let V0:=H V i; let O:=G; let q_ := z
    have hz: i∈ l++[i]:=by simp
    let m(t:I)(p:t∈ l):t∈ l++[i]:=List.mem_append_left _ p
    have sV(j)(p:j∈l):σ j=o:= t j (m j p)
    have h1:= ih sV (fun j l=> U j (m j l)) (fun j l=> w j (m j l))
    let P' := axle_P G Y.1; let Z(M:Rio I n)(s:Key J):= P' (Canz σ _ (pureX M) (Mκ s) z)
    let Vp(s):=PortJ Q VoxSpace (C i) (Platform Q (C i) P L) Y (ΛLine σ W0 Q0 Y (e s) X) z
    let g(s:Key J):=G (rite3 P Q L C Y l (Mκ s) (ΛLine σ W0 Q0 Y (e s) X) z); let g0(s:Key J):=G (Mκ s i • Vp s)
    have he(s): Z (Φ (R++(l++[i]))) s=Z V s+Z V0 s:=by
       unfold Z; rw[← List.append_assoc,Book3_cons,pureAdd3,puff_add]; apply map_add
    have hg(s:Key J): G (rite3 P Q L C Y (l++[i]) (Mκ s) (ΛLine σ W0 Q0 Y (e s) X) z)=g s + g0 s:=by
       unfold rite3; rw [List.map_append,List.sum_append,map_add]; change _+G (_+0)= _; rw[add_zero]; rfl
    change Kin id (fun s=> Z (Φ _) s) (fun s=> Z _ s + G (rite3 _ _ _ _ _ _ _ (ΛLine σ W0 Q0 Y (e s) X) _)); simp_rw[he,hg,←add_assoc]; apply loft_add (show Kin id (Z V) (fun x=> Z X x+g x) from h1) -- tune function.Cloak problem.
    let K:= Frame3 σ W0 Q0 V
    let b':= FortX3 F V
    have h4(s:Key J): yank K VoxPos (blank3 σ (σ i) (Mκ s)) Y= ΛLine σ W0 Q0 Y (e s) X:=by
       rw[t _ hz]; apply Eq.trans (vox_P σ W0 Q0 V _ Y (stern_R P σ F W0 Q0 Q L C S _).topP); exact (laneOn P σ F W0 Q0 Q L C S Y o R l sV (Mκ s)).1
    have hk:=pennPay3 Q K b' i σ VoxSpace VoxPos (legV σ W0 Q0 V) x a b h S Y G p (C i) (Platform Q (C i) P L) (U i hz) (w i hz) d (fun i=>turf3 σ W0 Q0 V Y v i) z -- args tune
    simp_rw [h4] at hk; exact hk
#print axioms StrideW
include T
set_option maxHeartbeats 270000 in
lemma StrideB (z:Force n): Kin (id:J→J) (fun i=>ag_top G Y (Canz σ _ (Book3 P σ F W0 Q0 Q L C S (R++l)).B (Reflect3 σ a b x i) z)) (fun s=>ag_top G Y (Canz σ _ (Book3 P σ F W0 Q0 Q L C S R).B (Reflect3 σ a b x s) z)+G (rime3 P Q L C Y l (Reflect3 σ a b x s) (ΛLine σ W0 Q0 Y (blank3 σ o (Reflect3 σ a b x s)) (Book3 P σ F W0 Q0 Q L C S R)) (ReefB σ F Y (blank3 σ o (Reflect3 σ a b x s)) (Book3 P σ F W0 Q0 Q L C S R)) z)):= by
 induction l using List.reverseRecOn with
 | nil=>
    simp only [List.append_nil, rime3, List.map_nil,List.sum_nil,map_zero, add_zero]; exact Kin.refl id (Connect.Hatch.rivers id _ (canH σ a h x b (axle_P G Y) (ax_s b G Y p) z _)) -- Type. p
 | append_singleton l i ih=>
    let X:= Φ R; let V:=Φ (R++l); let e(s:Key J):= Vζ s; let V0:=H V i; let O:=G; let q_ := z
    have hz: i∈ l++[i]:=by simp
    let m(t:I)(p:t∈ l):t∈ l++[i]:=List.mem_append_left _ p
    have sV(j)(p:j∈l):σ j=o:= t j (m j p)
    have h1:= ih sV (fun j l=> U j (m j l)) (fun j l=> w j (m j l))
    let P' := axle_P G Y; let Z(M:Rio I n)(s:Key J):= P' (Canz σ _ M.B (Mκ s) z)
    let Vp(s):=FrontJ Q VoxSpace (C i) (Platform Q (C i) P L) Y (ΛLine σ W0 Q0 Y (e s) X) (ReefB σ F Y (e s) X) z
    let g(s:Key J):=G (rime3 P Q L C Y l (Mκ s) (ΛLine σ W0 Q0 Y (e s) X) (ReefB σ F Y (e s) X) z); let g0(s:Key J):=G (Mκ s i • Vp s)
    have he(s): Z (Φ (R++(l++[i]))) s=Z V s+Z V0 s:=by
       unfold Z; rw[← List.append_assoc,Book3_cons,show (V+V0).B= V.B + V0.B from rfl,puff_add]; apply map_add
    have hg(s:Key J): G (rime3 P Q L C Y (l++[i]) (Mκ s) (ΛLine σ W0 Q0 Y (e s) X) (ReefB σ F Y (e s) X) z)=g s + g0 s:=by
       unfold rime3; rw [List.map_append,List.sum_append,map_add]; change _+G (_+0)= _; rw[add_zero]
    change Kin id (fun s=> Z (Φ _) s) (fun s=> Z _ s + G (rime3 _ _ _ _ _ _ _ (ΛLine σ W0 Q0 Y (e s) X) (ReefB σ F Y (e s) X) _)); simp_rw[he,hg,←add_assoc]; apply loft_add (show Kin id (Z V) (fun x=> Z X x+g x) from h1) -- tune function.Cloak problem.
    let K:= Frame3 σ W0 Q0 V
    let b':= FortX3 F V
    have h4(s:Key J): yank K VoxPos (blank3 σ (σ i) (Mκ s)) Y= ΛLine σ W0 Q0 Y (e s) X:=by
       rw[t _ hz]; apply Eq.trans (vox_P σ W0 Q0 V _ Y (stern_R P σ F W0 Q0 Q L C S _).topP); exact (laneOn P σ F W0 Q0 Q L C S Y o R l sV (Mκ s)).1
    have hk:=pennBeam3 Q K b' i σ VoxSpace VoxPos (legV σ W0 Q0 V) x a b h S Y G p (C i) (Platform Q (C i) P L) (U i hz) (w i hz) d (fun i=>turf3 σ W0 Q0 V Y v i) z -- args tune
    have h5(s:Key J): yankB (FortX3 F V) Y (blank3 σ (σ i) (Mκ s))= ReefB σ F Y (e s) X:=by
       rw[t _ hz]; apply Eq.trans (vox_B σ F V _ Y T (stern_R P σ F W0 Q0 Q L C S _).topB); exact (laneOn P σ F W0 Q0 Q L C S Y o R l sV (Mκ s)).2
    have hk5(s:Key J): yankB b' Y (blank3 σ (σ i) (Mκ s))= ReefB σ F Y (e s) X:= h5 s
    simp_rw [h4,hk5] at hk; exact hk
#print axioms StrideB
end
end
end Argos
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end
