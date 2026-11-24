import Organdy.Gala
import Organdy.Turpentine
import SatinThinIncense
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Organdy.Optic
open Function Filter MeasureTheory Finset

open Regis Head Lattice Precision Wilson Pressure Work.F03 Exterior
open Larva (Chip Tint dot blush stains decree wet_iff)
variable {n N:Side}
local notation "G" => SU.group

open RG Gleam ProbabilityTheory
open scoped InnerProductSpace ComplexConjugate
variable {M:Bed}{Z:PathData G}{q: Clip}{ρ θ v a η C:ℝ}


open Push.Local Next.Rank.Spindle Next.SectorChange
open Scree
open scoped Classical
variable {c:Side}{r:Ratio c n}{L:Support c}
  {α b ζ e k β τ:ℝ}{m l:ℕ}
  {W:Config G n→ℂ}{A:Ink (Chip n)}
  {R: Rules G}
  {F X Y:Larva.Dir n}{U:Config G n}{o:Site n}

def Onyx (r:Ratio c n)(L:Support c)(S:Support n)(m l:ℕ)(o:Site n):Prop:=
 ∀ w∈halo (l+2) {o}, withinCore r L S (hallBill m) w
lemma core_shines{S:Support n}{i:Site n}
 (p:withinCore r L S (hallBill m) i): Gleam.Safe r L 4 i:=p.1.shift (by simp [hallBill,Sequest];omega)
variable {S:Support n}
lemma workingHere {i:Bond n}
 (p: withinCore r L S (hallBill m) i.1):
 Working r L i:= ⟨p.1.1,rfl,(core_shines p).2 _ ((step_towards ..).trans (by norm_num))⟩

lemma silo (s:Signed)(o:Site n)(i:ℕ):
 (halo i {0}).image (turnSites s o)=halo i {o}:=by rw [Etch.halo_plan]; simp [affine]
lemma leafHere (s:Signed)
 (p:Onyx r L S m l o)
 (h:TrustLogs X U r L v) (g:v ≤ R.c):
  Agrees (halo l {(0:Site n)}) (pull s o U) (represent (bank s o X)):=by
 rw [show represent (bank s o X)=pull s o (represent X) from by simpa using bank_at s o X 1]
 apply agrees_pull
 rw [silo]
 intro i t _
 have y:i.1∈halo l {o}:=t
 obtain ⟨z,j,w⟩:=halo_spec.mp y
 obtain ⟨h₁,h₂⟩:= h i (workingHere (p i.1 (halo_spec.mpr ⟨_,j,w.trans (Nat.le_add_right l 2)⟩)))
 change _=(G).lieExp (collect G X i)*1
 rw [h₁,R.records _ (h₂.trans g),mul_one]

abbrev mists (τ:ℝ)(U:Config G n):Support n:=face_anchors (misdemean τ U)
lemma shiny {i:Cell n}
 (p:withinCore r L (mists τ U) (hallBill m) i.1): (G).chord (faceValue U i)≤τ:=by
 by_contra! h
 have hi:i∈misdemean τ U:=mem_filter.mpr ⟨mem_univ _,h⟩
 exact p.2 (halo_spec.mpr ⟨_,mem_image.mpr ⟨i,hi,rfl⟩,by simp⟩)

lemma rowHere (s:Signed)
 (p:Onyx r L (mists τ U) m l o)
 (g:Drier G τ U):
 pingS τ (halo l {(0:Site n)}) (pull s o U):=by
 intro i j; obtain ⟨w,tw,hw⟩:= Finset.not_disjoint_iff.mp j
 let y:=affine s o w; let z:=Face.send s o i
 have a:y∈touched z:=(Work.H03.touched_send s o i).symm ▸ mem_image.mpr ⟨_,hw,rfl⟩ -- rewrite
 have h:separation o y ≤ l:=by
   have b:y∈(halo l {0}).image (turnSites s o):=mem_image.mpr ⟨_,tw,rfl⟩
   simpa [silo,halo_spec] using b
 have c: z.1∈halo (l+2) {o}:=halo_spec.mpr ⟨_,mem_singleton_self _,(separation_triangle ..).trans (Nat.add_le_add h ((separation_comm ..).trans_le (Work.E01.sep_touched _ _ a)))⟩
 rw [Face.send_price U i s o (G).chord (G).chord_inv (fun k g=>(G).chord_conj g k)]
 exact lt_of_le_of_ne (shiny (p z.1 c)) (g z)

lemma probe_cost(p:0≤e)(h:ProbeBox X e):
  ‖X‖≤e:=by
 refine (pi_norm_le_iff_of_nonneg p).mpr ?_
 rintro ⟨i,k⟩ -- inspect
 simpa [collect, ←coord_map] using h (i,axisEquiv.symm k)

lemma sough_still (B:Z.Bounds q θ η C)(P:Attached M Z)
 (p:Onyx r L (mists τ U) m l o)
 (h:TrustLogs (X+Y) U r L v)(g:v≤R.c)(f:0≤v) (d:0≤e)
 (s:Signed)(b0:0<β){i:Chip n}(x:i∈stains 0 l) :
 let V:=sough q (e*coupling β) s o (starFeed B P r L (mists τ U) m Y β X) i
 V=e*blush (bank s o (X+Y)) i ∧ |V|≤e*(τ+faceCutError R v):=by
 intro V
 let j:=relay s o i
 have hp:withinCore r L (mists τ U) (hallBill m) j.1.1:=
   p _ (halo_spec.mpr ⟨o,mem_singleton_self _, relay_fee s o i (wet_iff.mp x)⟩)
 have hl:withinMark r L (mists τ U) m j.1:=hp.shift (by simp [hallBill])
 have ht:V=e*(draftSig s i * blush (X+Y) j):=by
    let V':=starFeed B P r L (mists τ U) m Y β X
    have a:Etch.river q j.1 V'= (coupling β)⁻¹ • faceCurl j.1 (X+Y):=by
       unfold V' starFeed
       rw [map_smul, Etch.river_still B P _ hl]

    have y:coupling β≠0:=(coupling_pos b0).ne'
    change e*coupling β*draftSig s i*(Etch.river q j.1 V') j.2=_
    rw [a]
    change _*((coupling β)⁻¹*blush (X+Y) j)=_
    field_simp
 rw [ht, blush_bank]
 refine ⟨rfl,?_⟩
 rw [abs_mul,abs_of_nonneg d,abs_mul,show |draftSig s i|=1 from turn_one ..,one_mul]
 apply mul_le_mul_of_nonneg_left _ d
 rw [←Real.norm_eq_abs]
 refine (PiLp.norm_apply_le (faceCurl j.1 (X+Y)) j.2).trans ?_
 let t:=(G).curvature (faceValue U j.1)
 calc
   _ ≤ ‖faceCurl j.1 (X+Y) - t‖ + ‖t‖ := norm_le_norm_sub_add ..
   _ ≤ faceCutError R v + τ := add_le_add
        ((norm_sub_rev ..).trans_le (angleFaceSmall h f g j.1 (core_shines hp)).2)
        (((G).curvature_norm _).trans (shiny hp))
   _ = _ := add_comm ..
