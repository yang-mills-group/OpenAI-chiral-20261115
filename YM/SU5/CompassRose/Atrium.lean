import YM.SU5.CompassRose.Boulevard

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 500000
set_option quotPrecheck false
set_option linter.unusedSectionVars false

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine Preparation.Yoke
open CF.Velvet CF.Pannier.Chancel CF.Pannier.Chancel.Rous Pressure
open YM.Stationary (Gaia)
open Onyx Regis.Circuit Regis.Head Regis.Head.Brecht Exterior Hiro

namespace Rose
open EmberWind Jewel
open Lamour Lamour.Bridge

-- Use `turn` ('negative' Step if true). Actual normalization includes the alternating-sign here
-- in the definition of WHERE to rent the face, so this *keg* reads positive-axis F convention
-- (for integral `clover` all four kegs get positive weight).
@[ext] structure Sconce where
  F : PlaqAxes
  i : Bool
  j : Bool
  spin : DirSpin
  w : Walk

namespace Sconce
open StressFlux (plate)
variable (B:Sconce)
abbrev v : Step := ⟨B.F.val.1,B.i⟩
abbrev u : Step := ⟨B.F.val.2,B.j⟩
abbrev C (a:Step) : Walk:= if a.neg then [a] else []
abbrev signs : ℝ := if B.i=B.j then 1 else -1
abbrev roads := (C B.v ++ C B.u : Walk)
abbrev border := B.w ++ roads B

def supportS (x:Cover) : Staff := ⟨nodeC x,x,(stop (nodeC x) (border B),B.F),B.spin,border B,rfl⟩
abbrev rent :ℕ:= B.w.length+6
lemma bordering : B.border.length ≤ B.w.length+2:=by
 unfold border roads; rw [List.length_append,List.length_append]; have hv(a:Step):(C a).length ≤1:=by cases e:a.neg<;> simp [C,e]
 have he:=(add_le_add (hv B.v) (hv B.u)); omega
lemma covered (x:Cover) (r:ℕ)(p:B.rent≤r): (supportS B x).Pays r r:=by
 let W:=B.border; have he:W.length+4 ≤ B.rent:=by unfold W rent; have hp:= B.bordering; omega
 have hv: ∀ (W:Walk)(x:Cover), stop x W ∈ visits x W:=by intro W; induction W with| nil=> intro; simp [visits,stop]| cons i w ih=> intro; simp [visits,stop,ih]
 exact ⟨(show W.length≤ r from by omega),fun i v=> pav_mono (show W.length≤r from by omega) (walk_pav _ _ W v), fun i h=> pav_mono (he.trans p) (span_walk _ (nodeC x) i W.length (square B.F.val.1 B.F.val.2) (walk_pav _ _ W (hv W (nodeC x))) (List.mem_toFinset.mp h))⟩
-- Actual Definition on a Mark. Implements native curvature staff: gauge Lie torsion at stop nodeC(u) along w.
variable {N:Side}(x:Cover)(U:Pane N)(ρ:ℝ)
abbrev origin {x:Cover} (B:Sconce)(U:Pane N): ColorL:= let y:=wrap (More N) (nodeC x); SU.group.adjoint (travel U y B.w) (StressFlux.plate U (stop y B.w) B.v B.u)
-- Adapted from Bloom.plateNext / plateWest (Thin/Slope/Sun.lean).
lemma road_fix (U:Pane N)(t:Seat N) : SU.group.adjoint (travel U t B.roads) (StressFlux.plate U (stop t B.roads) (posDir B.F.val.1) (posDir B.F.val.2))= B.signs • StressFlux.plate U t B.v B.u:=by
 let L:=SU.group.adjoint; have hx (x:Seat N)(i j:Step): SU.group.adjoint (i.read U x) (StressFlux.plate U (x+i.vec) i.rev j)= -StressFlux.plate U x i j:=by rw [StressFlux.plate_rev,map_neg,← Gauge.adjoint_mul,mul_inv_cancel]; simp
 have hp (x:Seat N)(i j:Step): SU.group.adjoint (j.read U x) (StressFlux.plate U (x+j.vec) i j.rev)=-StressFlux.plate U x i j:=by rw [StressFlux.plate_swap U (x+j.vec),map_neg,hx,StressFlux.plate_swap U x j i]; simp
 rcases B with ⟨F, (i|i), (j|j), spin,W⟩ -- rcases Bool ctor may not parenthesize
 · simp [roads,signs,C,v,u,stop,Lattice.travel]; try rfl
 · let a:=posDir F.val.1; let b:=negDir F.val.2; change SU.group.adjoint (b.read U t * 1) (StressFlux.plate U (t+b.vec) a b.rev)=(-1:ℝ) • StressFlux.plate U t a b; rw [mul_one,hp,neg_one_smul]
 · let a:=negDir F.val.1; let b:=posDir F.val.2; change SU.group.adjoint (a.read U t * 1) (StressFlux.plate U (t+a.vec) a.rev b)=(-1:ℝ) • StressFlux.plate U t a b; rw [mul_one,hx,neg_one_smul]
 let a:=negDir F.val.1; let b:=negDir F.val.2; change SU.group.adjoint (a.read U t * (b.read U (t+a.vec)*1)) (StressFlux.plate U (t+a.vec+b.vec) a.rev b.rev)=(1:ℝ) • StressFlux.plate U t a b; rw [mul_one,Gauge.adjoint_mul,hp,map_neg,hx,one_smul,neg_neg]
lemma keg_shown : (B.supportS x).edgeBudget ρ N U=ρ • B.signs • origin (x:=x) B U:=by
 let o:Seat N:=wrap (More N) (nodeC x)
 change SU.group.adjoint (travel U o B.border) (ρ • StressFlux.plate U (wrap (More N) (stop (nodeC x) B.border)) (posDir B.F.val.1) (posDir B.F.val.2))=_
 rw [wrap_stop_cover,map_smul]; change ρ • SU.group.adjoint _ (StressFlux.plate U (stop o (B.w ++ B.roads)) _ _)=_
 rw [border, travel_append, stop_append,Gauge.adjoint_mul, road_fix B U, map_smul]

abbrev up : Signed:= Signed.mirror 3
def waltz : Sconce := ⟨B.F,(B.v.rotate up).neg,(B.u.rotate up).neg,B.spin.swap, B.w.map (·.rotate up)⟩
lemma twice (x:Step): (x.rotate up).rotate up=x:=by cases x with|mk x y=> simp [up, Step.rotate, Signed.mirror]
@[simp] lemma spun_twice : B.waltz.waltz=B:=by
 have hx : B.waltz.waltz.w=B.w:=by unfold waltz; rw [List.map_map,show ((fun x:Step=> x.rotate up) ∘ (fun x:Step=> x.rotate up))=id from funext twice,List.map_id]
 refine Sconce.ext rfl ?_ ?_ rfl hx
 · exact congrArg Step.neg (twice B.v)
 exact congrArg Step.neg (twice B.u)
abbrev γ (z:ℤ) (x:Cover):= (plane 3 z).flee x
lemma pirouette (z:ℤ): origin (x:=x) B (fling 3 z N U)=origin (x:=γ z x) B.waltz U:=by
 let T:=plane 3 z; let c :=wrap (More N) (2 • (z • step (3:Axis)))
 let x₀:= nodeC x; let o:=wrap (More N) x₀; let W:= B.waltz; let A:=affine up c; have ht:A o=wrap (More N) (nodeC (γ z x)):= (((plane 3 z).anno x₀).trans (congrArg (wrap _) (T.mote _)))
 have he(V:Walk)(y:Seat N) : affine up c (stop y V)= stop (A y) (V.map (·.rotate up)):=by induction V generalizing y <;>  simp only [stop,List.map_cons,List.map_nil, *]; all_goals simp [A,affine,Step.vec_rotate,add_right_comm]
 rw [fling_eq]; unfold origin; dsimp only [waltz]
 rw [travel_pull,StressFlux.plate_pull]; dsimp only [up] at ht he; change (A o)=_ at ht; rw [he]; unfold A o x₀ up c at *; rw [ht]; rfl

@[simp] lemma rent_waves : B.waltz.rent=B.rent:=by unfold rent waltz; rw [List.length_map]
lemma sign_two : B.signs * B.signs=1:=by unfold signs; split <;> ring

-- Gauge mask & release. Keep every Pane, not a.e.
-- adapted from Thin/Slope/Zena.
private lemma meet_ping (t:ℝ)(S:Support (More N))(s:Signed)(p:Site (More N)) : pingS t S (pull s p U) ↔ pingS t (S.image (affine s p)) U:=by
 let A:=Face.send s p; have he:Surjective A:= Finite.surjective_of_injective (Face.injective_send s p)
 let T:= S.image (affine s p); have hv (i:Face (Per (More N))) : Disjoint S (touched i) ↔ Disjoint T (touched (A i)) := by unfold T A; rw [Work.H03.touched_send]; exact (disjoint_image (fun {_} {_} e=> s.act_injective (add_right_cancel e))).symm
 have ht (i:Face (Per (More N))) : SU.group.chord (faceValue (pull s p U) i)= SU.group.chord (faceValue U (A i)):= Face.send_price _ _ _ _ _ SU.group.chord_inv (fun i j=> Gauge.chord_conj _ j i)
 constructor; · intro w i v; obtain ⟨i,rfl⟩:= he i; rw [←ht]; exact w _ fun p=> v ((hv _).mp p)
 intro v i w; rw [ht]; exact v (A i) fun p=> w ((hv _).mpr p)
lemma mask_pitch (z:ℤ)(t:ℝ)(r:ℕ) : pingS t ((B.supportS x).gateS r N) (fling 3 z N U) ↔ pingS t ((B.waltz.supportS (γ z x)).gateS r N) U:=by
 rw [fling_eq,meet_ping]; unfold Staff.gateS; rw [← CF.Tye.dignify,image_singleton]
 exact ((show (plane 3 z).anon N ((wrap (More N)) (B.supportS x).hub)=(wrap (More N)) (B.waltz.supportS (γ z x)).hub from ((plane 3 z).anno _).trans (congrArg (wrap _) ((plane 3 z).mote x))) |> fun t=> by unfold Shape.anon plane at t; rw [t]) -- tune
lemma evening (t:ℝ)(z:ℤ)(r:ℕ):
    B.signs • (B.supportS x).pearl ρ N r t (fling 3 z N U) = B.waltz.signs • (B.waltz.supportS (γ z x)).pearl ρ N r t U :=by
 unfold Staff.pearl; rw [mask_pitch]; split
 · rw [keg_shown,keg_shown,B.pirouette]; rw [smul_comm B.signs,show B.signs • B.signs • _=origin (x:=γ z x) B.waltz U by rw [smul_smul,B.sign_two,one_smul],smul_comm B.waltz.signs ρ,show B.waltz.signs • B.waltz.signs • _=origin (x:=γ z x) B.waltz U by rw [smul_smul,B.waltz.sign_two,one_smul]] -- syntax infers placeholder?
 simp
-- For visitor X in Quay true signs and w nil. same Pauli here. signature normalization:
-- `shaded` has NO positive-orientation sign correction; uses the bare oriented plate (alternating sum for clover).
-- `supportS.rungWeave` includes the alternating sign. This distinction matters in Wake target.
abbrev shaded (r:ℕ)(t:ℝ): Papal.Weaver:= (B.signs:ℂ) • (B.supportS x).rungWeave ρ r t
lemma shaded_true (V:Fields N)(r:ℕ)(t:ℝ): B.shaded x ρ r t N V= wrapCurrent x B.spin 1 N (B.signs • (B.supportS x).pearl ρ N r t V.1):=by
 unfold shaded; simp only [map_smul,Pi.smul_apply,Staff.onMark]; rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]; rfl
-- Budget on station appointments with fixed winding attenuation. Exponent in phase H user can choose later
private lemma stop_walk (a b : Cover) (w:Walk): stop (a+b) w=stop a w+b:=by induction w generalizing a with|nil=>rfl|cons i w ih=>rw [stop,stop,add_right_comm a b,ih]
lemma obtains_at (P:Spine)(A:ℝ)(r:ℕ)(p:B.rent≤r)(t:0<A)(X:ℕ→ Cover)(D:Gaia)(h:Appoint P.par A X D) : LayoutBudget P A D (fun s=> B.supportS (X s)) (fun _=> r) (fun _=>r) B.F B.spin:=by
 let W(s:ℕ):=B.supportS (X s); refine ⟨fun s=> rfl,fun s=>rfl,h,?_, fun s=> B.covered _ _ p,?_⟩
 · let y:=stop (0:Cover) B.border; have hx(s:ℕ):(W s).face.1=y+nodeC (X s):=by change stop _ B.border=_; rw [← stop_walk,zero_add]
   let z:Gaia:=riseX 1 y; let M(s:ℕ):= sPow P.par s A
   have he:= ((tendsto_inv_atTop_zero.comp (sPower_pay P.par t)).smul_const z).add h; rw [zero_smul,zero_add] at he; apply he.congr; intro i; change (M i)⁻¹ • z+_=riseX _ (W i).face.1; rw [hx]; ext j; unfold z M; simp [riseX,gaugeRise,moor,div_eq_mul_inv]; ring
 have hx:= approved_visas P D h t B.F B.spin r r (by unfold rent at p; omega); exact hx.approved
#print axioms obtains_at
-- Why it turns as a genuine time-positive pair. proof follows Lycan.sz & CurrentClan models
-- (all spin labels visible, 10 and 5 normalized in same walk_star)
lemma pin_rate (j:SpinIdx)(i:Fin 2) : Mir.pin 3 j (upSpin i)=(if j=dnSpin i then 1 else 0) ∧ Mir.pin 3 j (dnSpin i)=(if j=upSpin i then -1 else 0):=by
 -- try economical proved parity columns first.
 have he : Mir.pin 3= !![ (0:ℂ),0,-1,0; 0,0,0,-1; 1,0,0,0; 0,1,0,0 ]:=by
    rw [Mir.pin]; rw [show gammaOp 3= gammaOp (Fin.succ (Fin.succ (Fin.succ 0))) from rfl]; change gammaOp ⟨3,by decide⟩ * grading= _
    ext i j; fin_cases i<;> fin_cases j<;> norm_num [gammaOp,grading,Matrix.mul_apply,SpinIdx,Fin.sum_univ_succ]
 rw [he]; fin_cases j<;> fin_cases i<;> exact ⟨rfl,rfl⟩
local notation "Bp0" p:max i:max => create (basisC N x (upSpin i) p)
local notation "Bp'" p:max i:max => Fock.remove (basisC N x (dnSpin i) p)
lemma rose_cr (V:ColorL)(b:DirSpin): wrapCurrent x b 1 N V=∑ p:SU.Slot,∑ q:SU.Slot, Hiro.walkC V p q • (Bp0 p b.1* Bp' q b.2):=by
 rw [Hiro.hold_sum]; apply sum_congr rfl; intro p _; apply sum_congr rfl; intro q _; have h: Twah.gold 1 =(-1:ℂ):=by simp [Twah.gold]
 change _ • (Twah.gold 1 • ((Bp' q b.2)* Bp0 p b.1))=_; rw [SitSpin.cr_swap,h,neg_one_smul,neg_neg]
lemma cr_turn (z:ℤ)(a b:Fin 2)(p q:SU.Slot) : Fock.theta (carR 3 z N) ((Bp0 p a)* Bp' q b)= create (basisC N (γ z x) (upSpin b) q) * Fock.remove (basisC N (γ z x) (dnSpin a) p):=by
 rw [theta_mul,(flips_basisC 3 z N x _ p).1, (flips_basisC 3 z N x _ q).2]
 simp_rw [(pin_rate _ _).1,(pin_rate _ _).2,ite_smul,zero_smul,sum_ite_eq',mem_univ,ite_true,one_smul,neg_one_smul]; rw [map_neg,smul_neg, mul_neg,Matrix.smul_mul,Matrix.mul_smul,smul_smul,neg_mul,Complex.I_mul_I,neg_neg,one_smul,SitSpin.cr_swap,neg_neg]
lemma ballad (z:ℤ)(r:ℕ)(t:ℝ) : fluent 3 z (B.shaded x ρ r t)=B.waltz.shaded (γ z x) ρ r t:=by
 funext n Y; unfold fluent reflMark; rw [shaded_true,shaded_true]; let W:= B.waltz; let V:= W.supportS (γ z x); let a:=W.signs • V.pearl ρ n r t Y.1; rw [show (reflFields 3 z Y).1= fling 3 z n Y.1 from rfl, evening]; change theta (carR 3 z n) (wrapCurrent _ _ _ _ a)=_
 rw [rose_cr,rose_cr]; simp_rw [theta_sum,theta_smul,cr_turn]; rw [Finset.sum_comm]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; rw [show star (walkC a j i)= walkC a i j from congrArg (fun A:Op _=> A i j) (walk_star a)]; try rfl
#print axioms ballad
end Sconce
end Rose
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
