import Organdy.Thrum
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Topology Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel
open Swell StressExchange Buffered
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra


open _root_.Zephyr.Chern
open Vale Py Py.Rate LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection

variable {N:Side}
local notation "Ω"=> Single N


variable {K:Scree.Loom N}{p:BudgetPoint}{X:SOp N}{o:Seat N}{a b d:ℝ}
/-- Translate a chime by a full sweep. Analytic accounting of its
profile uses 'julStep'; for the scalar we still have to apply
charge conjugation after 'julStep' (so sweeps with det=charge
really give a COMPLEX-LINEAR action). -/
abbrev cassette (s:Sweep N)(K:Scree.Loom N)(p:BudgetPoint)(o:Seat N)(X:SOp N) : Pane N→ℂ:=
    cSignX s.charge ∘ chime K p ((boxA s) o) (julStep s X)

lemma twist_free (U:UNI Ω)(k:Op Ω): Matrix.trace (twist U k) = Matrix.trace k:=by
 rw [twist_formula,Matrix.trace_mul_comm, ←mul_assoc,U.property.1,one_mul]
lemma ech_free (s:Sweep N)(k:Op Ω): Matrix.trace (ech s k) = cSignX s.charge (Matrix.trace k):=by rw [ech,singT,twist_free,win_trace]

lemma cassette_reads (st:StageSet K p d)
 (w:Trunk o X (p.B/10) a b d)(t:0≤a)
 (s:Sweep N): cassette s K p o X = chime K p o X ∘ flashA s:=by
 funext U
 have L:=jul_trunk s w
 let y:=(boxA s) o
 have B:(flashA s U ∈ safeZone p o) ↔ U∈safeZone p y:=by
    have e: actY s ({y}:Sa N)= {o}:=by simp [actY,y]
    have g:= glowA p.threshold (lensBox p.B y) s U
    change pingS _ (actY s (halo ..)) _ ↔_ at g
    rwa [←walkA,e] at g
 rw [cassette,comp_apply,comp_apply,chime,chime,←ech_free]
 congr 1
 by_cases r:U∈safeZone p y; swap
 · rw [shine,shine,Set.indicator_of_notMem r,Set.indicator_of_notMem (mt B.mp r),ech,singT,win_z,map_zero]
 obtain ⟨i,hi⟩:=(sepT (n:=N)).exists
 let z:=dressing st
 rw [frameLit z (trunks_canal w t) (B.mpr r) (bun s i),
    frameLit z (trunks_canal L t) r i]
 obtain ⟨t,d,q,g,-,-,-⟩:=st.lamps
 rw [g.move U i s hi]
 exact julius s X (K (U,i))
/-- The geometric H sweep, linear. Gauge origin 0 (not node 1). -/
abbrev polestar (N:Side)(s:Signed):Sweep N :=⟨s,0,detX s⟩
abbrev restL (N:Side)(s:Signed): Seat N:=boxA (polestar N s) (node 0)
lemma pole_zero(s:Signed):boxA (polestar N s) 0=0:=by
 rw [sitA]
 change affine _ ((assembly N).root 0) 0=0
 simp [affine]

lemma flashes_clear (s:Sweep N):flashA s 1 = 1:=by
   funext e; rw [flash]
   split <;> simp

lemma sep1 : separation (0:Site N) 1 ≤ 1:=by
    rw [separation_comm,separation,sub_zero,show (1:Site N)=wrap N 1 by ext; change (1:Per N)=((1:ℤ):Per N); simp] 
    apply Finset.sup_le
    intro i _
    exact (Corona.lap (n:=N) 1 i).trans (by decide : (1:ℤ).natAbs≤1) 

lemma home0 : node (0:Site N)=1:=by simpa using node_wrap N 0
lemma rest_short(s:Signed):separation 0 (restL N s)≤1:=by
    nth_rw 1 [←pole_zero (N:=N) s]
    unfold restL; rw [sitT,home0]
    exact sep1
lemma mildMore (o:Seat N)(h:separation 0 o≤1):
    Temper o (stream N) 64:=by
    refine ⟨by norm_num,fun v=> ((stream_mild N).grow v).trans ?_⟩
    have e:separation v.1 1 ≤ separation v.1 o + 2:=
        (separation_triangle ..).trans (add_le_add le_rfl ((separation_triangle _ 0 _).trans (add_le_add ((separation_comm ..).trans_le h) sep1)))
    have k: (separation v.1 1:ℝ) ≤ (separation v.1 o:ℝ)+2:=by exact_mod_cast e
    have g:(0:ℝ)≤ separation v.1 o:=by positivity
    linarith

/-- New occupant under a Sweep; exact movement on the Seats, including shifts
due to the location of the origin. -/
abbrev occupant (s:Sweep N) := (castX s).mills N
lemma movedMill (s:Sweep N) (y:Site N):
    ech s⁻¹ (millQ y)=millQ (occupant s y):=by
    have e: node (occupant s y)= boxA s (node y):=(castX s).nodex y

    have w:ech s (millQ (occupant s y))=millQ y:=by 
        rw [millSt,millSt,e]
        exact Tye.proM (boxA s) (boxA s).injective s.charge (γS s)
          (fun i j h=> Tye.birth_l i j _ _ _ h) _
    rw [←w,Sour.paceK,mul_inv_cancel, beat_x]

lemma nearbyMill (s:Signed)(m:ℕ)(y:Site N)(h:separation 0 y≤(12*m)):
    separation 0 (occupant (polestar N s) y) ≤ (12*m+1):=by
    let u:=occupant (polestar N s) y
    let T:=boxA (polestar N s)
    have e:node u=T (node y):=(castX (polestar N s)).nodex y
    have v:=rest_short (N:=N) s
    have g:separation (node (0:Site N)) (T (node 0)) ≤ 2:=(separation_triangle _ 0 _).trans
       (add_le_add ((separation_comm ..).trans_le (home0.symm ▸ sep1)) v)
    have a := separation_triangle (node (0:Site N)) (T (node 0)) (node u)
    nth_rw 1 [Hove.ζdist] at a
    rw [e,sitT,Hove.ζdist] at a
    -- rw e may fail when removes unique occurrence
    change separation 0 u ≤ _
    omega
