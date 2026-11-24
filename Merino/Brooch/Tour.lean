import Merino.Brooch.Guild
import YM.CF.BProof.Transit.Action
import Merino.Bias

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 520000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Brooch
open Function Finset Fock Scroll Spire Sault
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Lattice Cube Scree Skye Sour Drapes Tulip Lat Branch Swell
open Thera Hest Levier
variable {N:Side}
local notation "Jk"=> Single N

open Dial Vow
open Window BProof
 variable (s:Sweep N)


lemma s_wind {M:Finset Jk}{F:FC Jk}{i:Bool}
 (e:Fock.Sector M i F)(b:Bool):Fock.Sector M i (windX b F):=by
 induction e with
 | zero => simp [windX]; exact .zero _
 | one => rw [win_i]; exact .one
 | up i p => rw [win_up]; exact .up i p
 | down i p => rw [takeF,win_s,win_up]; exact .down i p
 | add _ _ x y=> rw [win_a]; exact x.add y
 | mul _ _ x y=> rw [win_m]; exact x.mul y
 | scale _ c x=> rw [win_c]; exact x.scale _

abbrev mount(s:Sweep N)(S:Support (More N)):=Bide.regionD s⁻¹ S

lemma moved {S:Support (More N)}{A:FC Jk} (e:Fock.Sector (modes S) false A):
 Fock.Sector (modes (mount s S)) false (move s A):=Bide.twist_sector (actR s) (actSpin s)
   (s_wind e (actB s)) (Bide.eligible ..)


lemma bra_transport {A B:FC Jk}
 (h:acts (star A) (mateK N)=acts (star B) (mateK N)):
 acts (star (move s A)) (mateK N) = acts (star (move s B)) (mateK N):=by
 let S:=actSpin s; let b:=actB s; let r:=actR s
 have hs(C:FC Jk):tourP S b r (star C)=star (move s C):=by
   change tourP S b r _=star (tourP S b r C)
   cases r
   · change twist _ (windX b _) = star _
     rw [win_s,map_star]; rfl
   · change theta _ (windX b _) = star _
     rw [win_s,theta_star]; rfl
 let q:=mateK N
 have hs0:arum S b r q q=q := arum_self _ _ _ (Tset N) ((touchP _) ▸ tickB _) (tickR (castX s⁻¹) (xtra b) (spinU b s⁻¹.s) (spinZ b s⁻¹.s) N)
 have ht(C:FC Jk):arum S b r q (acts (star C) q) =acts (star (move s C)) q:=by rw [arum_act,hs,hs0]
 unfold q at ht
 rw [←ht,←ht,h]


open Buffered
lemma region(S:Support (More N)):modes S=modesIn N S:=by
 ext i; simp [modesIn,matterSet,sitesIn]

lemma allowedX {F:Obs N}{S}(p:LicenseY S F):Allowed S F:=by
 refine ⟨p.bill,fun x y u=>p.loc.dep (x,x) (y,y) u u,?_⟩
 intro V; rw [region]; exact (p.loc.allV (V,V)).sector

lemma outAllowed {F:Obs N}{S}(p:Allowed S F):Allowed (mount s S) (Bide.move s⁻¹ F):=by
 let t:=s⁻¹
 refine ⟨?_,fun U V z=>congrArg (Hive.teen s⁻¹) (p.reads (flashA s⁻¹⁻¹ U) _ (flashD s⁻¹⁻¹ U V S ?_)),fun U=>moved s (p.modes_use _)⟩
 · let G:= F ∘ flashA t⁻¹
   exact Girt.pole_w (X:=FC Jk) G (Hive.teen t) (tour_c t.charge (detX t.s) _) (Girt.snap (X:=flashA t⁻¹) (F:=F) p.bounded (revM t⁻¹ |>.measurable))
 rwa [sitU s⁻¹]


open Tap Salt Tenant RG
lemma paneH (p:BudgetPoint)(x:Site N)(K:Scree.Loom N)(v:Orbit N)
 (F:LatticeFieldEstimates N)(A:phy N)(h:F v.1 (K v)=A v):
 paneMask p x true F v.1 (K v)=houseK p (offsetMask p.B x) A v:=by
 let B:Set (Pane N):= {U|pingS p.threshold (offsetMask p.B x) U}
 change B.indicator F v.1 _=_
 unfold houseK
 by_cases u:v.1∈B
 · have t:v∈pingMask p (offsetMask p.B x):=u
   rw [Set.indicator_of_mem u,Set.indicator_of_mem t];exact h
 have t:v∉pingMask p (offsetMask p.B x):=u
 rw [Set.indicator_of_notMem u,Set.indicator_of_notMem t]; rfl

variable (y:Spool N)(p:BudgetPoint)(K:Scree.Loom N)(z:ℝ)
abbrev spindle:=leanLatticeFieldEstimates p y.origin y.stepY y.spin y.color
lemma latticeFieldEstimates0(v:Orbit N):spindle y p v.1 (K v)=y.rift K p v:=by
 unfold spindle leanLatticeFieldEstimates Spool.rift puffLine
 simp only [Pi.add_apply]
 congr 1
 · apply paneH
   rfl
 unfold perWave highLine
 rw [Finset.sum_apply,Finset.sum_apply,Finset.sum_apply]
 refine sum_congr rfl ?_
 intro i _
 simp only [Pi.sub_apply]
 rw [boom,boom]
 unfold coverLine
 rw [paneH p _ K v, paneH p _ K v] <;> rfl


/-- physical -/
def face:Evaluation N:= Bide.move s⁻¹ (y.opening K p z)
/-- unphysical -/
def ghost:phy N:=(z:ℂ) • scene0 s K (spindle y p)
/-- support -/
def lashes:Support (More N):=mount s (y.canvas p)


abbrev behind(V:Orbit N):Orbit N:=(back s V.1,bun s V.2)
variable {K y p}{a b d:ℝ}(t:y.Hem K p a b d)
include t
lemma faceA:Allowed (lashes s y p) (face s y p K z):=outAllowed s (allowedX (t.licensed z))
lemma ghost_scales(V:Orbit N)(g:Injective (priorP V.2)):
 ghost s y p K z V=move s (y.release K p z (behind s V)):=by
 let w:=behind s V
 have e:K (behind s V)=back s (K V):=by
    obtain ⟨_,_,_,R,_⟩:=t.skylight.box
    exact R.move _ _ _ g
 have hh:cSignX ((actB s).xor (actR s)) z=z:=by cases ((actB s).xor (actR s)) <;> simp [cSignX]
 rw [Spool.release,Pi.smul_apply,move,sew_scale,hh,←latticeFieldEstimates0]
 rw [e];rfl


lemma ghostA (room:24*y.stepY≤p.B)(V:Orbit N)(g:Injective (priorP V.2)):
 Fock.Sector (modes (lashes s y p)) false (ghost s y p K z V):=by
 rw [ghost_scales s z t V g]
 apply moved
 rw [region]; exact t.occupies room (behind s V) z
lemma ghostYoke(V:Orbit N)(g:Injective (priorP V.2)):
 acts (star (face s y p K z V.1)) (mateK N)= acts (star (ghost s y p K z V)) (mateK N):=by
 rw [ghost_scales s z t V g]
 rw [show face s y p K z V.1 = move s (y.opening K p z (behind s V).1) from ?_]
 · exact bra_transport s ((t.yoke z) (behind s V))
 change move _ ((y.opening K p z) (flashA s⁻¹⁻¹ V.1))=_
 rw [inv_inv];rfl

end YM.CF.Merino.Brooch

