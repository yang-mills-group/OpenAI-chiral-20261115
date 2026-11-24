import Organdy.Ice
import Organdy.Hyssop
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Lattice Fock Sour Pastry Scree Skye Cadre Vow Palot Rue Tulip Lat Stax Rush Scroll Finset RG
open Cube Rill Mew Ione Bake Rive  Metric
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {n:Side} {p:BudgetPoint} {h a b c d:ℝ}{q:ℕ} {I : Type} [LinearOrder I] [Fintype I]

open Levier Urn Tenant Hake Salt Spire Nacre Dial SU
variable (s:Sweep n)
local notation "T"=> γS s
local notation "D₁" => detX s.s
local notation "B₁" => s.charge
local notation "JS"=> Single n
local notation "Fz"=> FC (Dwell n)

open Hive Phase Branch Cube
open Reed (Fine) -- tune syntax
open Buffered Sault Fock -- after Hive
local notation "Mk"=> FC (Single n)
local notation "J₂"=> Single n
local notation "f'" => twist T


section
variable {m:Type} [LinearOrder m][Fintype m] {Y Z S₀:Finset m}{x:Bool} {v:FC m} (r g:Bool) (u:UNI m)
lemma windP (i:m):windX r (put i)=put i:=by cases r; rfl; exact put_clear _
lemma wind_reg (p:Sector Y x v):Sector Y x (windX r v):=by
  induction p with
  |zero=>rw [win_z];exact Sector.zero _
  |one=>rw [win_i];exact Sector.one
  |up i h=>rw [windP];exact Sector.up i h
  |down i h=>rw [takeF,win_s,windP];exact Sector.down i h
  |add p q t w=>rw [win_a];exact t.add w
  |scale p z t=>rw [win_c];exact t.scale _
  |mul p q t w=>rw [win_m];exact t.mul w
lemma wind_vote (p:Fine S₀ Y x v):Fine S₀ Y x (windX r v):=by
  induction p with
  |empty=>rw [win_z];exact Fine.empty _
  |one=>rw [win_i];exact Fine.one
  |seed i h=>
    suffices k:windX r ((Reed.think S₀).term i)=(Reed.think S₀).term i by rw [k];exact Fine.seed i h
    by_cases u:i∈S₀
    · rw [show (Reed.think S₀).term i=put i from if_pos u,windP]
    rw [show (Reed.think S₀).term i= -takeF i from if_neg u,
        ←zero_sub,win_l,win_z,takeF,win_s,windP]

  |add p q t w=>rw [win_a];exact t.add w
  |scale p z t=>rw [win_c];exact t.scale _
  |grow p q t w=>rw [win_m];exact t.grow w

open BProof.Bide
lemma frame_turn (e:twist u (cutM Y)=cutM Z)
   (p:Sector Y x v):Sector Z x (Spire.tourP u r g v):=by
  cases g <;> exact twist_sector _ _ (wind_reg r p) e

lemma slalom (h:twist u (cutM S₀)=cutM S₀)
   (e:twist u (cutM Y)=cutM Z)
   (p:Fine S₀ Y x v):Fine S₀ Z x (twist (quantU u) v):=by
  induction p with
  |empty=>rw [map_zero];exact Fine.empty _
  |one=>rw [map_one];exact Fine.one
  |seed i p=>
    have hz {j:m} (l:j∈Z): Fine S₀ Z true ((Reed.think S₀).term j) := .seed j l
    by_cases g:i∈S₀
    · rw [show (Reed.think S₀).term i=put i from if_pos g,←create_put,twist_create,←prong_p,prong]
      apply Fine.sumF; intro j _
      by_cases w:u.val j i=0
      · rw [w, zero_smul]; exact Fine.empty _
      have ht:j∈ S₀:=by by_contra k;exact w (Reed.Fine.entry h g k)
      rw [←show (Reed.think S₀).term j=put j from if_pos ht]
      exact (hz (by by_contra k;exact w (Reed.Fine.entry e p k))).scale _

    rw [show (Reed.think S₀).term i= -takeF i from if_neg g,map_neg,←remove_take,twist_remove,←prong_t,prong, ←neg_one_smul ℂ]
    apply Fine.scale; apply Fine.sumF; intro j _
    by_cases w:u.val j i=0
    · rw [cc_apply,w,star_zero,zero_smul];exact Fine.empty _
    have h':twist u (cutM (S₀ᶜ))=cutM (S₀ᶜ):=by rw [dim_cut,map_sub,map_one,h]
    have ht:j∉ S₀:= mem_compl.mp (by by_contra k;exact w (Reed.Fine.entry h' (mem_compl.mpr g) k))
    have q:=hz (j:=j) (by by_contra k;exact w (Reed.Fine.entry e p k))
    rw [show (Reed.think S₀).term j= -takeF j from if_neg ht] at q
    exact (show Fine S₀ Z true (takeF j) from by simpa using q.scale (-1)).scale _
  |add p q t w=>rw [map_add];exact t.add w
  |scale p z t=>rw [twist_scalar];exact t.scale _
  |grow p q t w=>rw [map_mul];exact t.grow w

lemma wind_cut:windX r (cutM S₀)=cutM S₀:=by
  cases r; rfl
  ext i j
  change star (cutM S₀ i j)=_
  by_cases h:i=j <;> simp [cutM,h]

lemma prepaid (t:sings r u (cutM S₀)=swapX g (cutM S₀)) (e:twist u (cutM Y)=cutM Z)
   (p:Fine S₀ Y x v):Fine S₀ Z x (Spire.tourP u r g v):=by
   rw [singT,wind_cut] at t
   cases g
   · exact slalom u t e (wind_vote _ p)
   exact Reed.Fine.arrive e (by rw [dim_cut,map_sub,map_one,t,show swapX true _=1- _ from rfl];abel) (wind_vote _ p)

lemma norm_b (z:FC m):‖Spire.tourP u r g z‖=‖z‖:=by
  cases g
  · change ‖twist _ (windX _ _)‖=_; rw [twist_norm]
    cases r
    · rfl
    exact norm_cc _
  change ‖twist _ (cc (windX _ _))‖=_; rw [twist_norm,norm_cc]
  cases r; rfl; exact norm_cc _

lemma tour_fa (z:FC m):Spire.tourP u r g (star z)=star (Spire.tourP u r g z):=by
 cases g
 · change twist _ (windX _ (star _))=star (twist _ (windX _ _));rw [win_s,map_star]
 change twist _ (cc (windX _ (star _)))=star (twist _ (cc (windX _ _)));rw [win_s,cc_star,map_star]

end
 
local notation "tvl"=> Spire.tourP T B₁ D₁
local notation "mf" => mateK n
local notation "A₀" => arum T B₁ D₁ mf

lemma soothe : sings B₁ T (cutM (Tset n))=swapX D₁ (cutM (Tset n)) :=
   tickR (castX s) (xtra _) _ (spinZ ..) n

lemma autumns (C: Support (More n)):
   twist T (cutM (modesIn n C))=cutM (modesIn n (actY s C)):=by
  have e(S : Support (More n)) : modesIn n S=BProof.modes S:=by
    ext x; rw [modes_at,BProof.mem_modes]
  rw [e,e]
  exact BProof.Bide.eligible s (spinU B₁ s.s) C

lemma grounds : A₀ mf = mf :=
    arum_self T B₁ D₁ (Tset n) (touchP n ▸ tickB n) (soothe s)

abbrev voltaF (s:Sweep n)(u:Fields n): Fields n:=(flashA s u.1,flashA s u.2)
abbrev voltaM(s:Sweep n)(F:Mark n):Mark n := 
 fun z=> Hive.teen s (F (voltaF s⁻¹ z))

abbrev voltaU(s:Sweep n)(U:Swell.phy n):Swell.phy n :=
 fun z=> Hive.teen s (U (yellA s⁻¹ z)) -- correct namespace

lemma fullColor {F:Mark n}{C:Support (More n)}
  (f:AtSupport false C F)
  (g:covariant F):covariant (voltaM s F):=by
  intro w z
  -- v∘box s=w definition
  let v(i:Seat n):=(polarT s.charge).symm (w ((boxA s).symm i))
  let a:=voltaF s⁻¹ z
  have h:voltaF s a=z:=by simp [a,voltaF,lights,rev1]

  have eq:(fun i=> polarT s.charge (v (boxA s i)))=w:=by simp [v]
  have hs:voltaF s⁻¹ (simultaneous w z)=simultaneous v a:=by
    have e:voltaF s (simultaneous v a)=simultaneous w z:=by
      rw [←h]
      simp only [voltaF,simultaneous,Prod.map,revG,eq]
    rw [←e]; exact Prod.ext (revB ..) (revB ..)
  change teen s _= Hive.Gaze w (teen s _)
  rw [hs,g]
  have e:= yoT s v (F a) (BProof.Bide.Chord.keys_of_chord
     (BProof.Bide.Chord.full (f.allV a).sector))
  have y : ((polarT s.charge ∘ v)∘(castX s).anon n)=w:=eq
  rw [y] at e; exact e

lemma cymbalMoves {F:Mark n}{C:Support (More n)}{U:Swell.phy n}(v:Cymbal C F U a):
   Cymbal (actY s C) (voltaM s F) (voltaU s U) a:=by
  have h₀:∀ x:Fields n,‖voltaM s F x‖≤a:=fun x=>(norm_b _ _ _ _).le.trans (v.suprem _)
  have e:Continuous (voltaF s⁻¹):=((revM ..).comp continuous_fst).prodMk ((revM ..).comp continuous_snd)

  refine ⟨⟨⟨(tour_c _ _ _).measurable.comp (v.realc.env.meas.comp e.measurable),a,h₀⟩,
     fun x y p q=>congrArg (Hive.teen s) (v.realc.dep _ _ 
       (flashD s⁻¹ x.1 y.1 _ (by rw [sitU s];exact p))
       (flashD s⁻¹ x.2 y.2 _ (by rw [sitU s];exact q))),
     fun z=>prepaid _ _ _ (soothe s) (autumns s C) (v.realc.allV _)⟩,
    h₀,fullColor s v.realc v.color, fun _=>frame_turn _ _ _ (autumns s C) (v.spare _),
    fun W V X=>congrArg (Hive.teen s) (v.first ..),?_⟩
  intro z W
  let y:=yellA s⁻¹ z
  let x:=flashA s⁻¹ W
  change acts (star (tvl (F (y.1,x)))) mf=acts (star (tvl (U y))) mf
  have t:=congrArg A₀ (v.tie y x)
  rw [arum_act,arum_act,grounds, tour_fa,tour_fa] at t
  exact t
end YM.CF.Organdy
