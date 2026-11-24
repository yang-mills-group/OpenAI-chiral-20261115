import Organdy.Rows
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


variable {N:Side}{K:Scree.Loom N}{p:BudgetPoint}{X:SOp N}{J:Axis→ SOp N}{a b d:ℝ}{m:ℕ}
variable {o x:Site N}
local notation "Ω"=>Single N

/-- Raw prices; before the scalar normalizations (128)-(130). -/
abbrev Zc (K:Scree.Loom N)(p:BudgetPoint)(o:Site N)(X:SOp N):=
 clef (shine K p (node o) X)
abbrev Jc (K:Scree.Loom N)(p:BudgetPoint)(o:Site N)(X:SOp N):=
 harp (shine K p (node o) X)
abbrev Jd (K:Scree.Loom N)(p:BudgetPoint)(o x:Site N)(X:SOp N):=
 Jc K p x (co_Ψ x o X)
abbrev Jo (K:Scree.Loom N)(p:BudgetPoint)(o:Site N)(X:SOp N):=
 houseK p (offsetMask p.B o) (firePlate K X)
abbrev Jwind (K:Scree.Loom N)(p:BudgetPoint)(o:Site N)(J:Axis→ SOp N)(m:ℕ):=
 ∑ i:Axis,(Jd K p o (o+gapPlus i m) (J i)-Jd K p o (o-gapPlus i m) (J i))
abbrev Yc (K:Scree.Loom N)(p:BudgetPoint)(o:Site N)(J:Axis→ SOp N)(X:SOp N)(m:ℕ):=
 Zc K p o X + Jwind K p o J m

abbrev Zo (K:Scree.Loom N)(p:BudgetPoint)(o:Site N)(X:SOp N):=
 houseK p (offsetMask p.B o) (blazePlate K X)
variable (f:WindowDress K p d) (t:0≤a)
include f t

local notation "TT"=> Trunk (node o)
local notation "sizeD"=> (p.B/10)
local notation "glow"=> offsetMask p.B o
local notation "pp"=> pingMask p
lemma standZ (h:TT X sizeD a b d):
 Cymbal (foot p (node o)) (Zc K p o X) (Zo K p o X) b:=by
 have u:= trunks_canal h t
 refine slatClef (fun i=>?_) (slatLit f u)
 unfold Zo houseK
 by_cases w:i∈pp glow
 · rw [Set.indicator_of_mem w,frameLit f u w i.2]
 rw [Set.indicator_of_notMem w,shine,Set.indicator_of_notMem (show i.1∉safeZone p (node o) from w)]
 simp
lemma standJ (h:TT X sizeD a b d):
 Cymbal (foot p (node o)) (Jc K p o X) (Jo K p o X) (2*b):=by
 have u:=trunks_canal h t
 refine slatHarp (fun i=>?_) (slatLit f u)
 unfold Jo houseK
 by_cases w:i∈pp glow
 · rw [Set.indicator_of_mem w,frameLit f u w i.2]
 rw [Set.indicator_of_notMem w,shine,Set.indicator_of_notMem (show i.1∉safeZone p (node o) from w)]
 simp [dg,dyad]

/-- One fixed post-election b-collar, enlarged by inspection. Radius 2b if b ≫ m. -/
abbrev Porch(p:BudgetPoint)(o:Site N):=grooveB 2 p (node o)
variable (lot:24*m+4≤p.B)
omit f t
include lot
lemma fitsPorch (v:separation o x≤ m): foot p (node x) ⊆ Porch p o:=by
 intro i k
 obtain ⟨y,l,u⟩:=halo_spec.mp k

 rw [mem_singleton.mp l] at u
 refine halo_spec.mpr ⟨node o, mem_singleton_self _, (separation_triangle _ (node x) _).trans ((Nat.add_le_add_left u _).trans ?_)⟩
 -- check direction
 rw [Hove.ζdist]; omega

abbrev YcomCost(b:ℝ):= 2*(Tenant.quota^2*b)

include f t
lemma standJd (v:separation o x≤ m)(h:TT X sizeD a b d):
 Cymbal (Porch p o) (Jd K p o x X) (coverLine K p o x X) (YcomCost b):=
 (standJ f t (co_trunk x o h)).raise (fitsPorch lot v)

lemma standZo (h:TT X sizeD a b d):
 Cymbal (Porch p o) (Zc K p o X)
 (houseK p glow (blazePlate K X-barS0 N m o)) b:=by
 have l:separation o o≤ m:=by rw [separation_self]; omega
 have g:=(standZ f t h).raise (fitsPorch lot l)
 have hp:= barOrder o m (Porch p o)
    (lensBox_mono (node o) (show 24*m ≤ 2*p.B by omega))
 refine ⟨g.realc,g.suprem,g.color,?_,g.first,?_⟩
 · intro x; unfold houseK
   by_cases w:x∈pp glow
   · have u:= g.spare x; rw [Zo,houseK,Set.indicator_of_mem w] at u
     rw [Set.indicator_of_mem w, Pi.sub_apply,sub_eq_add_neg]
     exact u.add (by simpa using (hp x).1.scale (-1))
   rw [Set.indicator_of_notMem w]; exact Sector.zero _
 · intro x y; rw [g.tie,Zo,houseK,houseK]

   by_cases w:x∈pp glow
   · rw [Set.indicator_of_mem w, Set.indicator_of_mem w, Pi.sub_apply,star_sub,act_sub,(hp x).2,sub_zero]
   rw [Set.indicator_of_notMem w, Set.indicator_of_notMem w]

abbrev yInvoice(b:ℝ):= b+ 4*(YcomCost b+YcomCost b)
lemma standY (h:TT X sizeD a b d)(v:∀ i,TT (J i) sizeD a b d):
 Cymbal (Porch p o) (Yc K p o J X m) (puffLine K p o J X m) (yInvoice b):=by
 let u (i:Axis):= stopBeam o i m
 have r:= Cymbal.sum univ _ _ _ (fun i _=> (standJd f t lot (u i).1 (v i)).less
           (standJd f t lot (u i).2 (v i)))
 rw [show yInvoice b= b+∑ _i:Axis,(YcomCost b + YcomCost b) by simp [yInvoice,mul_add]]
 exact (standZo f t lot h).plus r
omit f t lot

variable (P:StageSet K p d)
lemma tick_step (t:Site N) :
    twist (γS (taxiPlus t)) (tickA N)=tickA N:=by
 let s:=taxiPlus t
 rw [touchP]
 have h:= tickR (castX s) (xtra false) (spinU false s.s) (spinZ false s.s) N
 rw [show detX s.s=false from det_i] at h; exact h

include P t
lemma stepLit (h:TT X sizeD a b d)(U:Pane N):
 let s:=taxiPlus (x-o)
 twist (γS s) (shine K p (node x) (co_Ψ x o X) U)=
    shine K p (node o) X (flashA s U):=by
 intro s
 have A : boxA s (node o)=node x:= by unfold s; rw [platforms,add_sub_cancel]
 have B:(flashA s U ∈ safeZone p (node o)) ↔ U∈safeZone p (node x):=by
    have e: actY s ({node x}:Sa N)= {node o}:=by rw [←A]; simp [actY]
    have g:= glowA p.threshold (offsetMask p.B x) s U
    change pingS _ (actY s (halo ..)) _ ↔_ at g
    rwa [←walkA,e] at g

 by_cases w:U∈safeZone p (node x); swap
 · rw [shine,shine,Set.indicator_of_notMem w,Set.indicator_of_notMem (mt B.mp w),map_zero]
 obtain ⟨i,hi⟩:=(sepT (n:=N)).exists
 let y:=dressing P
 rw [frameLit y (trunks_canal h t) (B.mpr w) (bun s i),
    frameLit y (trunks_canal (co_trunk x o h) t) w i]
 obtain ⟨t,d,q,r,-,-,-⟩:=P.lamps
 rw [r.move U i s hi]
 exact julius s X (K (U,i))

/-- Jd is the ACTUAL pose of Jc: pull the Pane by Sweep (taxiPlus
includes AP data), move letters back by quantized γ. -/
lemma poseJ (h:TT X sizeD a b d)(U:Fields N):
 let s:=taxiPlus (x-o)
 twist (quantU (γS s)) (Jd K p o x X U)= Jc K p o X
    (Prod.map (flashA s) (flashA s) U):=by
 intro s
 unfold Jd Jc harp
 rw [preJ_turn _ _ _ (tick_step (x-o)), stepLit t P h];rfl
