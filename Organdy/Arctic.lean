import Organdy.Northern
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


open Onyx Ember Lat Circuit Brecht
open Stationary (Gaia)
open scoped Topology 

variable {σ ε:ℝ}
-- Uniform angular chart
def Through (q:Clip)(σ η C ε r:ℝ)(I J:PlaqAxes):Prop:=
 ∀ (n:Side)(M:Bed)(R:ℝ)(z:Cover),
  Even n.val→M.covered σ C→Floor M q n η C→
  r ≤ R→R*pinch n≤r⁻¹→ ‖riseX R z-north‖≤r⁻¹→
  ‖magnify M R (plaquette I) (plaquette J) z n - specter I J north‖≤ ε

theorem crystals(q:Clip)(η:ℝ)(p:0<σ)(h:0<C)(e:0<ε)(I J:PlaqAxes):
  ∃r>0, Through q σ η C ε r I J:=by
 by_contra b; unfold Through at b; push Not at b
 let A(i:ℕ):ℝ:= i+1
 have aa:Tendsto A atTop atTop:=
    (tendsto_natCast_atTop_atTop (R:=ℝ)).atTop_add (tendsto_const_nhds (x:= (1:ℝ)))
 have ad:=tendsto_inv_atTop_zero.comp aa
 have active(i:ℕ):0<A i:=by unfold A; positivity
 choose V M R z v u a x y t φ using fun i=>b _ (active i)

 have w(i):0<R i:=(active i).trans_le (x i)
 have F:Yard V R:= ⟨w,tendsto_atTop_mono x aa,
    squeeze_zero (fun i=>mul_nonneg (w i).le (Ember.pinch_pos _).le) y ad,v⟩
 have g:Tendsto (fun i=>riseX (R i) (z i)) atTop (𝓝 north):=
    tendsto_iff_norm_sub_tendsto_zero.mpr
      (squeeze_zero (fun _=>norm_nonneg _) t ad)
 have ug:= mercury I J F g apart u a p h
 obtain ⟨i,ie⟩:=(Metric.tendsto_nhds.mp ug ε e).exists
 rw [dist_eq_norm] at ie
 exact not_lt_of_ge ie.le (φ i)

theorem halo_north(q:Clip)(η:ℝ)(p:0<σ)(h:0<C)(e:0<ε):
 ∃r>0, ∀I J, Through q σ η C ε r I J:=by
 have :∀ᶠ t in atTop, ∀I J, Through q σ η C ε t I J:=by
    apply eventually_all.mpr;intro I
    apply eventually_all.mpr;intro J
    obtain ⟨r,a,b⟩:=crystals q η p h e I J
    filter_upwards [eventually_ge_atTop r] with t t'
    have y:t⁻¹ ≤ r⁻¹:= inv_anti₀ a t'
    intro n M R z v u w l f g
    exact b n M R z v u w (t'.trans l) (f.trans y) (g.trans y)
 exact ((eventually_gt_atTop (0:ℝ)).and this).exists

lemma angle {x:Gaia}{h:ℝ}(e:0≤h)(g:∀i,|x i|≤h): ‖x‖≤2*h:=by
 rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), EuclideanSpace.real_norm_sq_eq]
 apply le_trans (sum_le_sum (g:=fun i:Axis=>h^2) (fun i _=>?_))
 · simp; ring_nf;first|rfl|simp [Axis]
 rw [←sq_abs]
 exact pow_le_pow_left₀ (abs_nonneg _) (g i) _

lemma farsight {x:Site n}{h:ℕ}(p: pdist x≤h)(i:Axis): |(Lattice.lift x i:ℝ)|≤h:=by
  have h': |Lattice.lift x i| ≤ h:= by rw [←Int.natCast_natAbs];exact_mod_cast ((component_le x i).trans p)
  exact_mod_cast h'

def ice (n:Side)(D:ℕ): Site n:=-(D • Lattice.step timeAxis)
def needle (D:ℕ)(x w:Site n):Cover:=
   Lattice.lift x+(D • Lattice.step timeAxis)-
     Lattice.lift (w-ice n D)
lemma fine (D:ℕ)(x w:Site n):x-w=wrap n (needle D x w):=by
  unfold needle; rw [map_sub,map_add,map_nsmul,wrap_step,wrap_lift,wrap_lift,ice]; abel

lemma east (i:Axis): ((Lattice.step timeAxis:Cover) i :ℝ)=north i:=by
 rw [Lattice.step_apply,north,basis_eq]
 split <;> simp [*,eq_comm]

variable {x w:Site n}{D k:ℕ}
lemma swing_north (d:0<(D:ℝ))(h:separation 0 x≤k)(g:separation (ice n D) w ≤ k+2):
 ‖riseX D (needle D x w)-north‖ ≤ 4*((k:ℝ)+1)/D:=by
 rw [show 4*((k:ℝ)+1)/D=2*((k+(k+2:ℕ):ℝ)/D) by push_cast;ring]
 refine angle (by positivity) (fun i=>?_)

 let a:= (Lattice.lift x i:ℝ)
 let b:= (Lattice.lift (w-ice n D) i:ℝ)
 have p:|a|≤k:=farsight (by rw [separation_comm,separation,sub_zero] at h; exact h) i
 have q:|b|≤(k+2:ℕ):=farsight ((separation_comm ..).trans_le g) i
 have e:(riseX D (needle D x w)-north) i = (a-b)/(D:ℝ) :=by
   change ((needle D x w i:ℝ)/(D:ℝ)-north i)=_
   simp only [needle, Pi.sub_apply,Pi.add_apply,Pi.smul_apply]
   simp only [nsmul_eq_mul]
   push_cast
   rw [east]
   unfold a b
   field_simp; ring
 rw [e,abs_div,abs_of_pos d]
 exact div_le_div_of_nonneg_right ((abs_sub ..).trans (add_le_add p q)) d.le

-- tip for using Through
variable {r:ℝ}

lemma beam_r (A J:PlaqAxes)(f:Through q σ η C ε r A J)
 (g:Even n.val)(z:M.covered σ C)(h:Floor M q n η C)(a:0<r)
 (b:r ≤ (D:ℝ))(u:D * pinch n≤r⁻¹)
 (off:4*((k:ℝ)+1)/D≤r⁻¹)
 (sx:separation 0 x≤k)(sy:separation (ice n D) w≤k+2):
 ‖(D:ℂ)^4 * rimble n M (x,plaquette A) (w,plaquette J)-specter A J north‖≤ ε:=by
 let t:=needle D x w
 have y:=f n M (↑D) t g z h b u ((swing_north (a.trans_le b) sx sy).trans off)
 unfold magnify at y
 rw [rimflare n M (wrap n t) 0 t (sub_zero _)] at y
 rw [rimflare n M x w t (fine D x w)]
 exact y

lemma flash_abs (A:PlaqAxes):|flash A|=1:=(congrArg (|·|) (flash_turn A)).symm.trans (turn_one ..)
lemma flashed (A J:PlaqAxes):
   (flash J:ℂ)* specter A J north=(if A=J then argent else 0):=by
   rw [beam_north]; split
   · unfold flash;split <;> push_cast <;> ring
   · simp
lemma glow (y:Site n)(i j:Chip n):
 ghost n M y i j=
    (sch («G»:=SU.group) i.2 j.2:ℂ)*(flash j.1.2 *
      rimble n M (i.1.1,plaquette i.1.2)
        ((relay mir y j).1.1,plaquette j.1.2)):=by
 have h:(relay mir y j).1.2=j.1.2:=mirror_rotate ..
 have e:(relay mir y j).2=j.2:=rfl
 rw [ghost,draftSig,flash_turn,glass,h,e]
 ring

lemma frosts (i j:Chip n):
  (sch («G»:=SU.group) i.2 j.2:ℂ)*(flash j.1.2*
      specter i.1.2 j.1.2 north)=
    (↑(argent * bell dot j (dot i)):ℂ):=by
 rw [flashed]
 classical
 simp only [bell,dot,Prod.mk.injEq,sch]
 split_ifs<;> simp_all

lemma wins (f:∀A J,Through q σ η C ε r A J)
 (g:Even n.val)(z:M.covered σ C)(h:Floor M q n η C)(a:0<r)
 (b:r ≤ (D:ℝ))(u:D * pinch n≤r⁻¹)
 (off:4*((k:ℝ)+1)/D≤r⁻¹):
 Whisper n M k D argent ε (ice n D):=by
 intro i x j y
 push_cast -- then frosts expects not cast?
 rw [glow]
 have e:=beam_r i.1.2 j.1.2 (f _ _) g z h a b u off (wet_iff.mp x)
      (relay_fee mir (ice n D) j (wet_iff.mp y))
 let γ:ℂ:= (sch («G»:=SU.group) i.2 j.2:ℂ)*flash j.1.2
 have n':‖γ‖ ≤ 1:=by unfold γ;rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,flash_abs]; unfold sch;split<;>norm_num
 rw [← Complex.ofReal_mul argent,← frosts]
 refine le_trans ?_ e
 -- scale

 let v:=(D:ℂ)^4 * rimble n M (i.1.1,plaquette i.1.2)
        ((relay mir (ice n D) j).1.1,plaquette j.1.2)-specter i.1.2 j.1.2 north
 have li:‖γ*v‖ ≤ ‖v‖:=by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) n'
 apply le_trans ?_ li; apply le_of_eq;apply congrArg; unfold γ v; ring
