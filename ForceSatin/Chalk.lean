import ForceSatin.PureLayout
import ForceSatin.Journal
import YM.SU5.Celeste.Claret
import Prism.Mill
set_option autoImplicit false
set_option maxHeartbeats 520000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
variable {h z:ℝ}
open Buffered
open CF.Pannier.Damask
open YM.CF.Velvet
open Pannier
namespace Papal
local notation "ℶ" => hat P.R.L P.x
local notation "💠" => P.K.j
open CF.Papyrus.Franc Verses CF.Pannier.Chancel Checkers Flint Gleam Gleam.Luster Gleam.Luster.Almanac Grade Graph
local notation "pio"=> P.R.L
open CF.Window CF.Velvet CF.Pannier.Damask

open CF.Papyrus.Franc.SatinForce
open Pannier
local notation "nₛ" s:max i:max => count Y s i
local notation "χf" x:max => parcelF x
open CF.Lamour CF.Lamour.Bridge.Celeste Afterglow Journey
-- Reflect only after switching, then return. Risa (proms) uses same sport team, here accurate THROUGH integralTill.
variable {N m':Side} {M:Tulip.Male} {d:ℝ} {m:ℕ} {K:Calibration}
lemma sea_mean {A:FC (Single N)} {z:ℂ} : fixedSeaMean M A z ↔ ∀ q:Wave _, Sea (FlatPaneP 4 M N) q→ z=alleyR (mateK N) q A:=by
 unfold fixedSeaMean; apply forall_congr'; intro q; apply imp_congr_right; intro _
 change _ ↔ z= (inner ℂ (mateK N) q)⁻¹*inner ℂ (mateK N) (acts A q); rw [div_eq_mul_inv,mul_comm]
lemma sea_zero_flip {A:FC (Single N)}(p:HaloTw 4 N)(h:fixedSeaMean M A 0)(a: Axis)(z:ℤ): fixedSeaMean M (theta (carR a z N) A) 0 := by
 apply sea_mean.mpr; intro q t; have he:=mirror_fare a z p t t (quietCon N A); change alleyR _ q (theta (carR a z N) A)=star (alleyR _ q A) at he; rw [← (sea_mean.mp h q t), star_zero] at he; exact he.symm
-- Q projector mean **exact** even in a dense reflected layout
structure Ticket (N: Side)(m:ℕ) (d:ℝ)(M:Tulip.Male) where
 S : Support (More N)
 val : FC (Single N)
 carries : AtSupport false S (quietCon N val)
 keeps : covariant (quietCon N val)
 paid : Street S m d val
 right : fixedSeaMean M val 0
-- all subsequent usage: at heat transcribed
namespace Ticket
def flip (p:HaloTw 4 N)(a:Axis) (z:ℤ)(x:Ticket N m d M): Ticket N m d M :=
 ⟨x.S.image ((Buffered.plane a z).anon N), theta (carR a z N) x.val,
   by rw [show quietCon _ (theta (carR a z N) x.val) = reflMark a z (quietCon N x.val) from rfl]; exact AtSupport.refl a z x.carries, by rw [show quietCon _ (theta (carR a z N) x.val) = reflMark a z (quietCon N x.val) from rfl]; exact covariant_reflected x.carries x.keeps z a,
   x.paid.reflect a z, sea_zero_flip p x.right a z⟩
def board (p:HaloTw 4 (K.c m')): Sport K m' (K.c m') (Ticket (K.c m') m d M) where
 place T := T.S
 pose T:= 1+quietCon _ T.val
 mirror a z x:= flip p a (Heat.gaugeShift K.B z) x
 castM _ z:= z
 stage _ _ o u:= ((AtSupport.oneM _).addM o.carries).mono u
 charge a z o _:=by
    funext x; let U:=carR a (Heat.gaugeShift K.B z) (K.c m'); change 1+theta U o.val=theta U (1+o.val); rw [theta_add,theta_one]
 town _ _ _:= rfl
lemma chess_strike {J:Type} (L:List J)(f: J→ FC (Single N)) (h:J→Mark N)(p:∀ i,h i=1+quietCon _ (f i)) :
   (L.map h).prod=quietCon _ (affineProd (f ∘ L.get) (List.finRange L.length) 1):=by
  rw [prod_finish]
  let g(j:J):=1+f j; have he : rollC (fun i:Fin L.length=>1+(Function.comp f L.get) i) (List.finRange L.length)=(L.map g).prod:=by
    unfold rollC; change ((List.finRange _).map (Function.comp g L.get)).prod=_; rw [←List.map_map]; rw [←List.ofFn_eq_map,List.ofFn_get] -- simp recursion?
  rw [he]; clear he
  funext x; change _= (L.map g).prod; induction L with
  | nil=>rfl
  | cons j L ih=>rw [List.map_cons,List.prod_cons,Pi.mul_apply,p j, ih]; rfl
lemma chess_books {s i k:ℕ}(L:List (Ticket (count Y s i) m d (gram Y s i k).J.M))(u:L.Pairwise (Disjoint on Ticket.S)) (p:180^m*d ≤ pencilPrice (ℶ s)) :
   PureBooks Y s i k m (List.finRange L.length) (Ticket.val ∘ L.get) (fun _=>0) 0:=by
 let f:=Ticket.val ∘ L.get; let Z:=List.finRange L.length; let S(j:Fin L.length):= modesIn (count Y s i) (L.get j).S
 have he(a b:Fin L.length)(p:a≠b) : Disjoint (S a) (S b):= by
   have h:Disjoint (L.get a).S (L.get b).S:= (lt_or_gt_of_ne p).elim (fun x=> u.rel_get_of_lt x) (fun x=> Disjoint.symm (u.rel_get_of_lt x))
   apply disjoint_left.mpr; intro i v w; exact disjoint_left.mp h ((modes_at ..).mp v) ((modes_at ..).mp w)
 refine ⟨List.nodup_finRange _, fun a _ b _=>?_, ⟨S,(fun x _ y _ z=> he x y z),fun i _=>⟨(L.get i).keeps,Credential.enlarge p (L.get i).paid.harvest,(L.get i).right⟩⟩,by simp⟩
 by_cases h:a=b; · subst b; exact rfl
 let U:Fields (count Y s i):=(1,1); have hx:= ((L.get a).carries.allV U).sector.apart ((L.get b).carries.allV U).sector (he a b h); exact hx.trans (one_smul ℂ (f b*f a))
lemma portrait (X:Ticket N m d M): ∀ i:Fields N,‖(1+quietCon _ X.val:Mark N) i‖ ≤ Real.exp (180^m*d):=by
 intro i; let K₀:=tailor (1:UNI (Single N)); have hv:fiber K₀ 1:=by constructor <;> intro i <;> simp [basisKet, K₀,tailor] -- name
 have hg:‖X.val‖ ≤ (180:ℝ)^m*d :=by
    have h:= Credential.glow X.paid.harvest hv le_rfl; rw [one_pow,mul_one, show K₀.glow X.val=X.val from ?_] at h; exact h
    unfold K₀ Shaft.glow tailor; dsimp only; change quant 1*_ *quant (star 1)=_; rw [star_one,quant_one,one_mul,mul_one]
 exact (norm_add_le ..).trans ((add_le_add (le_of_eq norm_one) hg).trans (((Real.add_one_le_exp ((180:ℝ)^m*d))).trans' (le_of_eq (add_comm ..))))
lemma switched {m':Side} {K:Calibration} (U : Mark N→ℂ)(Z:Mark N→ℂ) (lV:ℝ)(g:N=K.c m') (A₀:HaloTw 4 N) (q:Twosome K N U)(w:0<lV)(X:Ticket N m d M) (x poseHere:ℝ)
 (lo:∀ F:Mark N,Envelope F→(∀ i, ‖F i‖ ≤ Real.exp (x * sites N))→ ‖Z F-U F‖ ≤ lV)
 (h:∀ L:List (Ticket N m d M), sites N ≤ L.length * poseTill ((poseHere):ℝ) → -- add poseHere parameter
   L.Pairwise (Disjoint on Ticket.S) → ‖Z (quietCon N (affineProd (Ticket.val ∘ L.get) (List.finRange L.length) 1))‖ ≤ Real.exp (L.length*lV))
 (b:ℕ)(p:b+addgap K≤ N.val)(u: (↑(4*(b+addgap K):ℕ):ℝ)^4 ≤ poseTill ((poseHere):ℝ)) (c:∀ i,cows i X.S b)(W:180^m*d ≤ x):
    ‖Z (1+ quietCon _ X.val)‖ ≤ Real.exp (3*lV) := by
 subst N; let N:=K.c m'; let S:=(board (K:=K) (m':=m') A₀ : Sport K m' N (Ticket N m d M)); let F:= 1+ quietCon N X.val; let T:=sites N
 have he: Sport.race S [X]:=List.pairwise_singleton _ _
 obtain ⟨n,L,G,H,P,Q,V⟩:= Sport.team S U q [X] p (fun i=>by change cows i (X.S ∪ ∅) b; simpa using c i) he
 rw [List.length_singleton,mul_one] at Q
 let t:ℝ:= L.length; have hz:t≥1:=by unfold t; rw [Q]; push_cast; exact one_le_pow₀ (one_le_pow₀ (by norm_num))
 have hl:t≤T:=by unfold t T sites; rw [Q]; exact_mod_cast G
 rw [show Sport.film S [X]=F from mul_one F,←Q] at V
 let A:= Sport.film S L
 have hu:‖Z A-U A‖≤lV:=by
    have he(L:List (Ticket N m d M)) : Envelope (Sport.film S L) ∧ ∀ i:Fields N,‖Sport.film S L i‖≤Real.exp (x*L.length):=by induction L with
    | nil=> exact ⟨(AtSupport.oneM univ).env,fun i=>by change ‖(1:FC _)‖ ≤ _; rw [norm_one]; simp⟩
    | cons i L ih=>
       let f:=1+ quietCon N i.val; let F:=Sport.film S L
       change Envelope (f*F) ∧ _
       refine ⟨env_mult ((AtSupport.oneM _).addM i.carries).env ih.1, fun z=>?_⟩
       change ‖f z * F z‖ ≤ _
       apply (norm_mul_le ..).trans; apply (mul_le_mul ((i.portrait z).trans (Real.exp_monotone W)) (ih.2 z) (norm_nonneg _) (Real.exp_pos _).le).trans; apply Eq.le; rw [←Real.exp_add,List.length_cons,Nat.cast_add,Nat.cast_one,mul_add,mul_one,add_comm]
    exact lo A (he L).1 (fun i=> ((he L).2 i).trans (Real.exp_monotone (mul_le_mul_of_nonneg_left hl (le_trans (mul_nonneg (by positivity) X.paid.nonneg) W))))
 have hz': T ≤ t*(↑(4*(b+addgap K):ℕ):ℝ)^4:=by unfold T t sites; rw [Q]; exact_mod_cast H
 have hg: ‖Z A‖≤ Real.exp (t*lV):=by
   unfold A Sport.film; rw [chess_strike L Ticket.val S.pose (fun _=>rfl)]; apply h L (hz'.trans (mul_le_mul_of_nonneg_left u (zero_le_one.trans hz))) P
 have hw:L.length≠0:=by intro e; unfold t at hz; rw [e] at hz; norm_num at hz
 have hw: ‖U F‖≤ Real.exp (2*lV):=by
    apply le_of_pow_le_pow_left₀ hw (Real.exp_pos _).le (V.trans ((norm_le_norm_sub_add (U A) (Z A)).trans _))
    rw [norm_sub_rev,←Real.exp_nat_mul, show (L.length:ℝ)*(2*lV)=t*lV+t*lV from (by unfold t; ring),Real.exp_add]
    have hh:lV+1≤Real.exp (t*lV):=(add_le_add_left (le_mul_of_one_le_left w.le hz) _).trans (Real.add_one_le_exp _); nlinarith only [hh,hu,hg,w]
 have hv: ‖Z F-U F‖ ≤ lV:= lo F ((AtSupport.oneM _).addM X.carries).env (fun i=> (portrait X i).trans (Real.exp_monotone (W.trans (le_mul_of_one_le_right (le_trans (mul_nonneg (by positivity) X.paid.nonneg) W) (hz.trans hl)))))
 refine (norm_le_norm_sub_add (Z F) (U F)).trans ((add_le_add hv hw).trans ?_); rw [show 3*lV=2*lV+lV from (by ring),Real.exp_add]; nlinarith only [Real.one_le_exp (show 0≤ 2*lV by positivity),Real.add_one_le_exp lV,w]
#print axioms switched
end Ticket
end Papal
end LocalLimit
end Rate
end YM.CF.Py
