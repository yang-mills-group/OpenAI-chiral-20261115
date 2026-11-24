import YM.SU5.FiniteGaugeData.Signal.Trumpet
import YM.SU5.FiniteGaugeData.Signal.Metropolis
/-! # Limiting state compatibility of activated nonzero signal. This one state at all floors/moments.
 Physical `Y.Λ` pivot predates all floors or tv shrink. Accountant error μ on μ period & sharp path,
 witness transported actual at fixed separation **NOT renormalized to UV margin through inverse graft**.
 Lease dimensions always confirmed through assignment; only claim sterile read regarding means of special
 unbalanced chiral class. Continuum, vacuum and OS strict correlation not asserted by this result.
 -/
set_option autoImplicit false
set_option linter.flexible false
set_option maxHeartbeats 760000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Signal
open Function Filter NormedSpace MeasureTheory Finset Lattice RG Wilson Fock Lat Cube SU Scroll Spire Tulip
open Window Mir Skye Scree Rush Dial Laic Thera Nacre Drapes Paige Vault Peaks Cascade Hive
open Buffered Buffered.Afterglow Buffered.Advance Reef Hom Tenant Branch Buffered.Concord Buffered.Afterglow.Satin Lifted
open MeasureTheory Push.SectorMeasure Girt
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix MatrixOrder ComplexOrder Kronecker Classical Matrix.Norms.L2Operator ComplexConjugate Pointwise
attribute [local instance] opCStarAlgebra
open Supplies Sparkle Sparkle.Condense Sparkle.Portage Sparkle.Circuit Pastel Momentum Furnace
open Scherzo Kinetic Play Py Py.Rate LocalLimit Preparation Skyscraper IgnoreFog Vale Period
open Buffered.Reliance Buffered.Reliance.ShortWave Afterglow Afterglow.Journey
open Boon Graph Pressure Esti Jade.Earn Phase CF.Laic CF.Ember
open Escalator Concord Boon Parfume
namespace Ovation
namespace Transit
variable {N:Side}{K:Calibration} -- status
variable (S T:Finset Cover) (L:List Cover) (l:SU.Slot)
variable {f:Mark N}

lemma parked (T':Evaluation N)(L:Loom N)(D:Orbit N→ Phys N) {v:Finset (Site N)}{r:List (Site N)}
    (p:∀ x:Pane N,T' x∈ generous (family l) v r)(h:r.Nodup)(u:r≠[]) (t:∀ i∈r,i∉v)
    (R:∀ i j,T' i=T' j) (V:Plum.Rotate D) : markedRead (toMark T') L D=0:=by
 cases r with
 | nil=> contradiction
 | cons i r=>
    let X:= markedRead (toMark T') L D; let U:= lamp i
    have hp: (star (zeta l)) * X = 1*X:= by unfold X; rw [one_mul, ←mark_smul, ←Plum.track T' L D U V]; congr 1; funext y; change star (zeta l) • T' y.1= twist (quantU (tradew N U)) (T' (gauge U⁻¹ y.1)); unfold U; rw [R (gauge _ y.1) y.1]; have ht:=keyGrace i l v (t i List.mem_cons_self) (i::r) h (p y.1); rw [if_pos List.mem_cons_self] at ht; exact (show twist _ _= _ from ht).symm -- tune
    by_contra! v; exact charge_one l (mul_right_cancel₀ (show X≠0 from v) hp)

lemma room_read (K:Calibration)(m:Side)(u:Shelter T S L)(v:Hosp T (K.c m))(r:L≠[]) :
    ∃ i:Site (K.c m), generous (family l) (S.image (wrap (K.c m))) (L.map (wrap (K.c m)))≤ Key (quantU (tradew (K.c m) (lamp i))) (star (zeta l)):=by
 cases L with
 | nil=>contradiction
 | cons i L=>
   let N:= K.c m; let J:=i::L; let f:= wrap N; have hs(x:Cover)(p:x∈J):x∈browse T:= (inside_b ..).2 (u.2.1 x p); let X:= (IgnoreFog.sole v); rw [List.map_cons]; refine ⟨f i,?_⟩; have h: f i∉ S.image f:=fun p=> by obtain ⟨j,p,v⟩:=mem_image.mp p; exact (u.2.2.2 i List.mem_cons_self) ((X ((inside_b ..).2 (u.1 j p)) (hs i List.mem_cons_self) v) ▸ p)
   have hl:(J.map f).Nodup:= u.2.2.1.map_on (fun a p b q=> X (hs a p) (hs b q)); exact (keyGrace (f i) l _ h ((f i)::L.map f) hl).trans_eq (by rw [if_pos List.mem_cons_self])
lemma pop (x:Site N)(v: List (Site N))(S:Finset (Site N)){X:FC (Single N)}(p: generous (family l) S v ≤ Key (quantU (tradew N (lamp x))) (star (zeta l)))(e:X∈generous (family l) S v) (t: twist (quantU (tradew N (lamp x))) X=X) : X=0:=by
 rw [show twist _ X=_ from (show twist _ X=_ from p e)] at t; by_contra! h; apply charge_one l; exact (smul_left_injective ℂ h) (t.trans (one_smul ℂ X).symm)
-- factorized independent classifications impossible for nonzero image on any roomy schedule, by covariance
lemma gauged (K:Calibration)(m:Side)(x:junior K)(v:Shelter T S L)(h: Hosp T (K.c m))(r:L≠[])(p:Effect K l S T L x)(e:x≠0) : ¬(∀ y z,x.val m y=x.val m z):=by
 intro f; let N:= K.c m; let W:= x.val; obtain ⟨i,q⟩:= room_read S T L l K m v h r; let U:=quantU (tradew N (lamp i)); have he:x.val m=0:=by
    funext V; refine pop l i (L.map (wrap N)) _ q ((secure K (family l) S T L v.1 v.2.1 p.wild).2.2 m V) ?_; exact ((show Gaugeable x from p.key) m (lamp i) V).symm.trans (f _ _)
 exact e (Subtype.ext (native_ext T K h p.opera InTest.zero he))
-- matter insertion transported basis
variable (K:Calibration)(P:Preparation) (M:ℕ) {s d k:ℕ} {N n:Side}{L₁:Loom N}
lemma conceded (t:K.c n=N) (S T:Finset Cover) (L:List Cover)(f:Buffered.Family K)(l:SU.Slot) (w:Shelter T S L) (p:L≠[]) (u:f∈ Parfume.price K (family l) S L) (R:Hosp T (K.c n)){Ψ:Orbit N→ Phys N}(A:Plum.Rotate Ψ) : markedRead (t ▸ f n) L₁ Ψ=0:=by
 subst N; let g:= f n 1; let T':= fun x:Pane (K.c n)=>g; have he:f n=toMark T':=funext fun x=> (show InTest K true T false f∧_ from stern K (family l) S T L w.1 w.2.1 u).2 n x 1
 let V:= L.map (wrap (K.c n)); let N:= K.c n; let Q:=S.image (wrap N); rw [he]; apply parked (v:=Q) l T' L₁ Ψ (fun _=>?_) ?_ (show V≠[] from by unfold V; simpa) ?_ (fun _ _=>rfl) A -- removed P
 · exact (w.2.2.1.map_on fun i p j u=> (sole R) ((inside_b ..).2 (w.2.1 i p)) ((inside_b ..).2 (w.2.1 j u))) -- order
 · intro i k; obtain ⟨j,u,rfl⟩:=List.mem_map.mp k; change _∉ Q; intro t; obtain ⟨i,k,e⟩:=mem_image.mp t; exact w.2.2.2 j u ((sole R ((inside_b ..).2 (w.1 i k)) ((inside_b ..).2 (w.2.1 j u)) e) ▸ k)
 change f n 1∈ generous (family l) (S.image (wrap (K.c n))) V; rw [←price_result K (family l) n S L 1]; exact Submodule.mem_map_of_mem u
end Transit
end Ovation
end YM.CF.Signal
#print axioms YM.CF.Signal.Ovation.Transit.gauged
#print axioms YM.CF.Signal.Ovation.Transit.conceded
