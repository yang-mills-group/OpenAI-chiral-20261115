import YM.SatinExist.Rutabaga
import YM.SatinExist.Zurna
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 330000
set_option maxRecDepth 4000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark.Rutabaga
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common CF.Pannier.Chancel
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis Again
open CF.Lamour CF.Lamour.Bridge.Celeste Sonnet
private lemma ascent {x y:ℕ}(p:0<y)(v:y≤x):∃ k:ℕ, 2^k*y ≤ x ∧ x≤2*2^k*y:=by
  have he : x < 2^x*y:= lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.le_mul_of_pos_right _ p)
  let P(k:ℕ):= x ≤ 2*(2^k)*y
  have ht: ∃ k,P k:=⟨x,by unfold P; linarith⟩
  refine ⟨Nat.find ht,?_,Nat.find_spec ht⟩
  generalize e: Nat.find ht=k
  cases k with
  | zero=> simpa using v
  | succ k=> have h:=Nat.find_min ht (by omega : k < Nat.find ht); change ¬ x ≤ 2*2^k*y at h; rw [pow_succ']; omega
variable {K:Calibration}{N:Side}{M:Tulip.Male}{c f v z:ℝ}{p k r d B:ℕ}
private lemma lengths (A : List (Sonnet N))(q:SpotP.Sylvia k r d p M f v c z A): A.length≤ (More N).val^4:=by
 let L:= A.map (fun i=>i.o); have hp:L.Nodup:=by
    apply List.pairwise_map.mpr
    refine q.annex.imp_of_mem ?_
    intro i j g h e u
    have hp:=e i.o (q.core i g).slotT _ (q.core _ h).slotT; rw [u,separation_self] at hp; omega
 have h:= hp.length_le_card
 unfold L at h; simpa [Seat,Four,Axis,Per] using h
-- budget Pastry at f=v. request slack scaled to σ=1
abbrev volumePrice (K:Calibration)(w B:ℕ) :=16*(16*K.B.val*w)*(2*(B+addgap K))^3
open Papal
-- use bound as repeat relation & truth
variable {Λ: Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K'"=>tent Y H
local notation "j₀"=> Λ.K.j
abbrev knownM (i k w:ℕ)(p r d:ℕ)(ε ξ C θ:ℝ) := ∀ U : List (Sonnet (side Y i w)), SpotP.Sylvia Λ.K.j r d p (gram Y w i k).J.M ε ξ C 1 U → ‖Journey.compass Y i k w (buffet U)‖ ≤ Real.exp (θ*((More (side Y i w)).val:ℝ)^4)
variable (p r d:ℕ)(ε ξ C:ℝ) (z:ℝ)
include H
abbrev Yθ : ℝ:=Real.exp 1
-- bounds
variable {p r d v' w' i s:ℕ}
lemma ticket (k:ℕ) (α:Ferry Y s i k)(e:IcePlot Y s i k)(Hc: HaloTw Λ.K.j (side Y i s))
   {p r d:ℕ} (h: knownM Y i k s p r d ε ξ C z)(u:0≤z)(q: z*(volumePrice (tent Y H) w' B:ℝ) ≤ 1)
   (S:Family (tent Y H))(Q:Cover)(j:Axis)(H0:Start j Q (distribute Y H s i) Λ.K.j r d p (gram Y s i k).J.M ε ξ C 1 B 0 (ruler (tent Y H).B*(w':ℤ)) 1 S)
   (w₀:0<w')(B0: B+addgap (tent Y H) ≤ (side Y i s).val)
   (hc:0≤C)(V:1*(16/Yθ) ≤ ((side Y i s).val:ℝ))
   {n:ℕ}(hn:0<n)
   (g:2*(ruler (tent Y H).B*w'*n) ≤ ((side Y i s).val:ℤ))(g₁: ((side Y i s).val:ℤ) ≤ 4*(ruler (tent Y H).B*w'*n))(a:ℤ):
    ‖hot Y H s i k (banner j w' ((w':ℤ)*a) n S)‖ ≤ ((2*Real.exp 1)^2)^(2*n):=by
 let T:=distribute Y H s i; let u0:=solder Y i k α.depth s; let N:=Journey.side Y i s
 let W₀:=distribute_arith Y H s i
 obtain ⟨L,o,hv,L',S0⟩:= largeL j Q T (fun f g=>(W₀ _ _ 0).2.1) (W₀ 1 1 1).2.2.2.1 (fun a F=>(W₀ F F 0).2.2.2.2 _ _) Hc (w':ℕ) (by exact_mod_cast w₀) H0 g ((w':ℤ)*a)
 let R':= SlabMark.banner j (w':ℤ) ((w':ℤ)*a) n S
 have t:T R'= buffet L:= L'
 obtain ⟨D,vD,Dh⟩:= ascent (show 0<B+addgap K' from (Nat.add_pos_right _ addgap_pos)) B0
 let K1:= Finset.univ.erase j; obtain ⟨U,A,hU,Uh⟩:=SpotP.scatter (ν:=u0) Hc (revive Y H _ _ _ α) (terrain Y H _ s).symm vD K1 L o (fun i v=> S0 i (mem_erase.mp v).1); rw [show K1.card=3 from (by simp [K1,Axis])] at hU Uh
 rw [hv] at hU
 let l:= (2^D)^3; let x:=U.length; let G:=Yθ
 have Hp:0<l:=by unfold l; positivity
 have HG:0<G:=by unfold G Yθ; positivity
 have hx:N.val ≤ (4*n)*(16*(K').B.val*w'):=by
    apply Int.ofNat_le.mp; push_cast; exact g₁.trans_eq (by unfold ruler; ring)
 have he:(More N).val^4 ≤ x*volumePrice K' w' B:=by
    change (N.val*2)^4 ≤_
    let a:=16*(K').B.val*w'; let b:= B+addgap K'
    have he: N.val ≤ 2^D*(2*b):= Dh.trans_eq (by unfold b; ring)
    calc
       _ = 16 * (N.val*N.val^3) := by ring
       _ ≤ 16 *((4*n * a)*(2^D*(2*b))^3):= by gcongr -- tune
       _ = x * volumePrice K' w' B:=by unfold x volumePrice a b; rw [hU]; ring
 have hY:‖u0 (buffet U)‖ ≤ (2*G)^x:=by
    let f:= Journey.compass Y i k s
    have he': ‖f (buffet U)‖ ≤ G^x:=by
       refine (h U A).trans ?_; unfold G Yθ; rw [←Real.exp_nat_mul]; apply Real.exp_monotone
       calc
          _≤ z*((x:ℝ)*volumePrice K' w' B):= by gcongr; exact_mod_cast he
          _= (x:ℝ)*(z*volumePrice K' w' B):= by ring
          _≤ _:= mul_le_mul_of_nonneg_left q (by positivity)
    have hx':‖f (buffet U)-u0 (buffet U)‖ ≤ G^x:= (e α.depth _ (1^x) A.occupy.env (fun V=>by obtain ⟨h,e,u⟩:= SpotP.larder U A V; rw [e,norm_smul,norm_one,mul_one,one_pow]; exact u)).trans (Yoke.hailW Y i HG (by norm_num : (0:ℝ)≤1) V (lengths U A))
    have hx:0 < x:=by unfold x; rw [hU]; positivity
    refine (norm_le_norm_sub_add (u0 _) (f (buffet U))).trans ?_; rw [norm_sub_rev,mul_pow]; exact (add_le_add hx' he').trans ((by rw [←two_mul]; apply mul_le_mul_of_nonneg_right _ (pow_nonneg HG.le _); simpa only [pow_one] using (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hx) : G^x+G^x ≤ 2^x*G^x)) -- flips using Cauchy
 rw [hot,dif_pos α.depth]; change ‖u0 (T R')‖ ≤ _; rw [t, ←pow_mul,show 2*(2*n)=4*n from by omega];
 apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (n:=l) Hp.ne').mp
 exact Uh.trans (hY.trans_eq (by unfold x G Yθ l; rw [hU, Nat.mul_comm (_^3) (4*n),pow_mul])) -- exponent order
end YM.CF.Buffered.Afterglow.Tower.SlabMark.Rutabaga
