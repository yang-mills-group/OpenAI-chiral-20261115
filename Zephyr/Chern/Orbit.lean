import Zephyr.Chern.Facing
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern

open YM YM.Lattice Filter Topology Silk YM.CF YM.CF.Fir YM.Next.Free YM.CF.Jill


variable {j:ℕ} {r:Male→Streams}

lemma Looming.j_origin (p:Looming j r) (hj:1≤j) (i:Male) : E 0 (jac (r i))=1 := by
  rw [jac, AlgHom.map_det]
  have e: (E 0).mapMatrix (frameM (r i))=1 := by
    ext a b
    change E 0 (frameM (r i) a b) = _
    rw [Matrix.one_apply]
    induction a using Fin.cases
    · rw [frame_0]
      induction b using Fin.cases
      · rw [(p.origin i).1, if_pos rfl]
      · simp [(p.origin i).2,Ne.symm (Fin.succ_ne_zero _)]
    rw [frame_succ]
    induction b using Fin.cases
    · simp [p.normal]
    dsimp only
    simp [p.tangent hj]
  rw [e,Matrix.det_one]

variable {I:Type*} {F:Filter I} {z:I→Streams} {q:Streams}

lemma arrives_jac (h:∀k,Arrives F (fun i=>z i k) (q k)) :
    Arrives F (fun i=>jac (z i)) (jac q) := by
  have e a b : Arrives F (fun i=>frameM (z i) a b) (frameM q a b) := by
    induction a using Fin.cases
    · exact h b
    · exact (h b).D _
  simp only [jac, Matrix.det_apply']
  exact Arrives.sum _ (fun _=>Arrives.mul (arrives_const ..) (Arrives.prod _ (fun k=>e _ _)))

variable {n:I→Male}

lemma Looming.polar [F.NeBot] (p:Looming j r) (hj:1≤j)
    (h:∀k, Arrives F (fun i=>r (n i) k) (q k)) : Polar q where
  sphere := by
    have e : Arrives F (fun i=>r (n i) ⬝ᵥ r (n i)) (q ⬝ᵥ q) :=
      Arrives.sum _ (fun k=>(h k).mul (h k))
    apply Silk.ext; funext x
    exact tendsto_nhds_unique_of_eventuallyEq (e.co x) tendsto_const_nhds
      (Eventually.of_forall fun i=>congrArg (fun s:Silk=>s.co x) (p.round _).1)
  peak := tendsto_nhds_unique_of_eventuallyEq (Arrives.E (h 0) 0)
    tendsto_const_nhds (Eventually.of_forall fun _=>(p.origin _).1)
  real t:= tendsto_nhds_unique_of_eventuallyEq (Complex.continuous_im.continuousAt.tendsto.comp
    (Arrives.E (h 0) t)) tendsto_const_nhds (Eventually.of_forall fun _=>((p.round _).2 t).1)
  bottom t:= ge_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp
    (Arrives.E (h 0) t)) (Eventually.of_forall fun _=>((p.round _).2 t).2)
  avoid t a := by
    obtain ⟨u,b,g⟩:=p.dip hj t a
    exact lt_of_le_of_lt (le_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp
      (Arrives.E (h 0) t)) (Eventually.of_forall fun _=>g _)) b

  facing := by
    have d : E 0 (jac q)= 1 :=
      tendsto_nhds_unique_of_eventuallyEq (Arrives.E (arrives_jac h) 0)
        tendsto_const_nhds (Eventually.of_forall fun _=>p.j_origin hj _)
    simp [d]

/-- convergence of the whole history family along *any* ultrafilter,
with positive top-form average in the limit (also for each individual history). -/
theorem Looming.passes (p:Looming j r) (hj:1≤j) (L: Ultrafilter I) (m:I→Male) :
    ∃ q, (∀ k, Arrives L (fun i=>r (m i) k) (q k)) ∧ Polar q := by
  choose q eq using fun k => Swift.arrive (L:=L) ((p.moves k).comp (n:=m) le_top)
  exact ⟨q, eq, p.polar hj eq⟩

theorem Looming.margin (p:Looming j r) (hj:1≤j) :
    ∃ c:ℝ,0<c ∧ ∀ i,(τ (jac (r i))).re ≥ c := by
  by_contra! b
  choose m h using fun n:ℕ=> b (1/(n+1)) (by positivity)
  obtain ⟨q,g,hq⟩:=p.passes hj (Ultrafilter.of atTop) m
  have c:= (arrives_jac g).co 0
  have e : (τ (jac q)).re ≤ 0 :=
    le_of_tendsto_of_tendsto' (Complex.continuous_re.continuousAt.tendsto.comp c)
      (tendsto_one_div_add_atTop_nhds_zero_nat.mono_left (Ultrafilter.of_le atTop))
      fun i=>(h i).le
  exact (hq.price.not_ge e).elim
