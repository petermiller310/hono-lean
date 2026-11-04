// Native source evidence, separate from the Lean kernel theorem.
const { splitPath } = await import(Bun.argv[2])
const document = JSON.parse(await Bun.stdin.text())
const fromUnits = (units: number[]): string => {
  let result = ''
  for (const unit of units) result += String.fromCharCode(unit)
  return result
}
const toUnits = (text: string): number[] => {
  const result = []
  for (let index = 0; index < text.length; index++) result.push(text.charCodeAt(index))
  return result
}
const results = document.inputs.map((units: number[]) => {
  const input = fromUnits(units)
  // The default case runs the actual imported upstream function. Small explicit
  // limits separately check intrinsic ordering with the same source operations.
  if (document.limit === 4294967295) return splitPath(input).map(toUnits)
  const pieces = input.split('/', document.limit)
  if (pieces[0] === '') pieces.shift()
  return pieces.map(toUnits)
})
console.log(JSON.stringify({ runtime: Bun.version, results }))
