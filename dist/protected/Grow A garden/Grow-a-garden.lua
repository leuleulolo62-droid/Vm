-- ===== Key System (must pass before the script runs) =====
local function __y2k_keygate()
-- ============================================================================
--  Y2k key provider  (drop-in replacement for the Junkie SDK)
--  Talks to YOUR Cloudflare Worker + KV key server (server-side hashing, HWID
--  auto-bind, expiry). CONFIGURE the two URLs below. Server: server-example/.
-- ============================================================================
local Junkie = {}
do
	local KEY_API  = "https://y2k-keys.y2kscript.workers.dev"  -- your deployed Worker (LIVE)
	local KEY_LINK = "https://work.ink/2Dgt/ks-int12887-kq76mlra7lo" -- work.ink key link

	local HttpService = game:GetService("HttpService")
	local function enc(s) local ok, r = pcall(function() return HttpService:UrlEncode(s) end) return ok and r or s end
	local function httpGet(u)
		for _, f in ipairs({
			function() return game:HttpGetAsync(u) end,
			function() return game:HttpGet(u) end,
			function() return request and request({ Url = u, Method = "GET" }).Body end,
		}) do
			local ok, b = pcall(f); if ok and type(b) == "string" then return b end
		end
		return nil
	end
	local function hwid()
		local id
		pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
		if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
		return tostring(id or "unknown")
	end

	function Junkie.get_key_link() return KEY_LINK end
	function Junkie.check_key(key)
		if not key or key == "" then return { valid = false, message = "No key entered" } end
		local hw = hwid()
		local url = KEY_API .. "/check?key=" .. enc(key) .. "&hwid=" .. enc(hw) .. "&t=" .. tostring(os.time())
		local body = httpGet(url)
		if not body then return { valid = false, message = "Key server unreachable" } end
		local b = string.lower(body)
		if string.find(b, "ok", 1, true) then
			getgenv().HWID = hw
			return { valid = true, message = "KEY_VALID", hwid = hw }
		elseif string.find(b, "expired", 1, true) then
			return { valid = false, message = "Key expired" }
		elseif string.find(b, "hwid", 1, true) then
			return { valid = false, message = "Key locked to another device" }
		else
			return { valid = false, message = "Invalid key" }
		end
	end
end


local TweenService = game:GetService("TweenService")
local UserInputService = game:GetService("UserInputService")
local RunService = game:GetService("RunService")
local Players = game:GetService("Players")
local Lighting = game:GetService("Lighting")
local HttpService = game:GetService("HttpService")

local Icons = {
	Shield = "rbxassetid://105619007041452",
	Loading = "rbxassetid://116535712789945",
	Lock = "rbxassetid://114355063515473",
	Key = "rbxassetid://93569468678423",
	Check = "rbxassetid://119783053916823",
	CheckCircle = "rbxassetid://10709790644",
	XCircle = "rbxassetid://10747384394",
	Warning = "rbxassetid://130226573962640",
	Globe = "rbxassetid://10734950309",
	Info = "rbxassetid://94529541997278",
	ExternalLink = "rbxassetid://71038734318580",
	Copy = "rbxassetid://107485544510830",
	Spinner = "rbxassetid://10709767827",
	Database = "rbxassetid://114209748010261",
	Sparkles = "rbxassetid://10709767827",
	ErrorFolder = "rbxassetid://113312905787220",
	Candy = "rbxassetid://10709767827",
	JunkieNewIcon = "rbxassetid://75038032192167"
}

local function hasFileSystemSupport()
    local hasWritefile = pcall(function() return type(writefile) == "function" end)
    local hasReadfile = pcall(function() return type(readfile) == "function" end)
    local hasIsfile = pcall(function() return type(isfile) == "function" end)
    return hasWritefile and hasReadfile and hasIsfile
end

local fileSystemSupported = hasFileSystemSupport()

local function saveVerifiedKey(key)
    if not fileSystemSupported then return false end
    local ok = pcall(function()
        writefile("verified_key.txt", key)
    end)
    return ok
end

local function loadVerifiedKey()
    if not fileSystemSupported then 
        return nil 
    end
    
    local ok, content = pcall(function()
        return readfile("verified_key.txt")
    end)
    
    if not ok or not content then 
        return nil 
    end
    return content
end

local function clearSavedKey()
    if not fileSystemSupported then return false end
    local ok = pcall(function() delfile("verified_key.txt") end)
    return ok
end

local Configuration = {
	ScreenGuiName = "JunkieKeySystem",
	Window = {Size = UDim2.new(0, 333, 0, 500)},
	Colors = {
		Bg = Color3.fromRGB(12, 12, 12),
		Primary = Color3.fromRGB(59, 130, 246),
		PrimaryDark = Color3.fromRGB(37, 99, 235),
		StatusIdle = Color3.fromRGB(249, 115, 22),
		StatusSuccess = Color3.fromRGB(16, 185, 129),
		StatusError = Color3.fromRGB(239, 68, 68),
		StatusVerifying = Color3.fromRGB(59, 130, 246),
		StatusWarning = Color3.fromRGB(254, 188, 46),
		TextMain = Color3.fromRGB(255, 255, 255),
		TextSec = Color3.fromRGB(161, 161, 170),
		TextMuted = Color3.fromRGB(113, 113, 122),
		Border = Color3.fromRGB(255, 255, 255),
		TrafficRed = Color3.fromRGB(255, 95, 87),
		TrafficYellow = Color3.fromRGB(254, 188, 46),
		TrafficGreen = Color3.fromRGB(40, 200, 64),
		Success = Color3.fromRGB(50, 205, 110),
		Error = Color3.fromRGB(245, 70, 90),
		Warning = Color3.fromRGB(255, 200, 50)
	},
	BorderTransparency = 0.15,
	Animations = {
		VeryFast = 0.1,
		Fast = 0.2,
		Medium = 0.4,
		Slow = 0.5,
		VerySlow = 0.6,
		Bounce = 0.6
	},
	Fonts = {
		Title = 24,
		Subtitle = 12,
		Button = 14,
		Input = 16,
		Body = 13,
		Small = 11,
		Tiny = 12
	}
}

local Utils = {}

Utils.Tween = function(obj, props, time, style, dir)
	local t =
		TweenService:Create(
		obj,
		TweenInfo.new(time or 0.3, style or Enum.EasingStyle.Quint, dir or Enum.EasingDirection.Out),
		props
	)
	t:Play()
	return t
end

Utils.CreateCorner = function(parent, radius)
	local corner = Instance.new("UICorner")
	corner.CornerRadius = UDim.new(0, radius or Configuration.CornerRadius)
	corner.Parent = parent
	return corner
end

Utils.Round = function(obj, radius)
	local c = Instance.new("UICorner")
	c.CornerRadius = UDim.new(0, radius or 12)
	c.Parent = obj
	return c
end

Utils.TweenBack = function(instance, properties, duration)
	return Utils.Tween(instance, properties, duration, Enum.EasingStyle.Back, Enum.EasingDirection.Out)
end

Utils.CreateStroke = function(parent, color, thickness, transparency)
	local stroke = Instance.new("UIStroke")
	stroke.Color = color or Configuration.Colors.Border
	stroke.Thickness = thickness or 1
	stroke.Transparency = transparency or 0.77
	stroke.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	stroke.Parent = parent
	return stroke
end

Utils.Stroke = function(obj, color, thick, trans)
	local s = Instance.new("UIStroke")
	s.Color = color or Color3.new(1, 1, 1)
	s.Thickness = thick or 1
	s.Transparency = trans or 0.9
	s.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	s.Parent = obj
	return s
end

Utils.CreateGradient = function(parent, color1, color2, rotation)
	local gradient = Instance.new("UIGradient")
	gradient.Color =
		ColorSequence.new(
		{
			ColorSequenceKeypoint.new(0, color1),
			ColorSequenceKeypoint.new(1, color2)
		}
	)
	gradient.Rotation = rotation or 300
	gradient.Parent = parent
	return gradient
end

local function SetBlur(enabled)
	local blur = Lighting:FindFirstChild("JunkieBlur")
	if enabled then
		if not blur then
			blur = Instance.new("BlurEffect")
			blur.Name = "JunkieBlur"
			blur.Size = 0
			blur.Parent = Lighting
		end
		Utils.Tween(blur, {Size = 24}, Configuration.Animations.Bounce)
	elseif blur then
		Utils.Tween(blur, {Size = 0}, Configuration.Animations.Medium)
		task.delay(
			0.4,
			function()
				blur:Destroy()
			end
		)
	end
end

local ToastSystem = {ActiveToasts = {}, MaxToasts = 3, ToastSpacing = 10}

ToastSystem.Create = function(parent, message, toastType, duration, statusCode)
	local colors = {
		success = Configuration.Colors.Success,
		error = Configuration.Colors.Error,
		warning = Configuration.Colors.Warning,
		info = Configuration.Colors.Primary
	}
	local icons = {
		success = Icons.CheckCircle,
		error = Icons.ErrorFolder,
		warning = Icons.Warning,
		info = Icons.Info
	}
	local toastColor = colors[toastType] or colors.Bg
	local toastIcon = icons[toastType] or nil
	if #ToastSystem.ActiveToasts >= ToastSystem.MaxToasts then
		local oldest = table.remove(ToastSystem.ActiveToasts, 1)
		if oldest and oldest.Parent then
			oldest:Destroy()
		end
	end
	local toastHeight = 56
	local toast = Instance.new("Frame")
	toast.Name = tick()
	toast.Size = UDim2.new(0, 0, 0, toastHeight)
	toast.Position = UDim2.new(0.5, 0, 0, 20)
	toast.AnchorPoint = Vector2.new(0.5, 0)
	toast.BackgroundColor3 = Configuration.Colors.Bg
	toast.BackgroundTransparency = 0.5
	toast.BorderSizePixel = 0
	toast.ZIndex = 300
	toast.ClipsDescendants = true
	toast.Parent = parent
	Utils.Round(toast, 14)
	Utils.CreateStroke(toast, toastColor, 1, 0.1)
	Utils.CreateGradient(toast, Configuration.Colors.Bg, Configuration.Colors.Bg, 1)
	local iconBg = Instance.new("Frame")
	iconBg.Name = "IconBg"
	iconBg.Size = UDim2.new(0, 36, 0, 36)
	iconBg.Position = UDim2.new(0, 12, 0.5, 0)
	iconBg.AnchorPoint = Vector2.new(0, 0.5)
	iconBg.BackgroundColor3 = toastColor
	iconBg.BackgroundTransparency = 0.85
	iconBg.BorderSizePixel = 0
	iconBg.ZIndex = 301
	iconBg.Parent = toast
	Utils.Round(iconBg, 18)
	local icon = Instance.new("ImageLabel")
	icon.Name = "Icon"
	icon.Size = UDim2.new(0, 20, 0, 20)
	icon.Position = UDim2.new(0.5, 0, 0.5, 0)
	icon.AnchorPoint = Vector2.new(0.5, 0.5)
	icon.BackgroundTransparency = 1
	icon.Image = toastIcon
	icon.ImageColor3 = toastColor
	icon.ZIndex = 302
	icon.Parent = iconBg
	local textContainer = Instance.new("Frame")
	textContainer.Name = "TextContainer"
	textContainer.Size = UDim2.new(1, statusCode and -110 or -60, 1, 0)
	textContainer.Position = UDim2.new(0, 56, 0, 0)
	textContainer.BackgroundTransparency = 1
	textContainer.ZIndex = 301
	textContainer.Parent = toast
	local text = Instance.new("TextLabel")
	text.Name = "Message"
	text.Size = UDim2.new(1, 0, 1, 0)
	text.BackgroundTransparency = 1
	text.Text = message or ""
	text.TextColor3 = Configuration.Colors.TextMain
	text.TextSize = Configuration.Fonts.Body
	text.Font = Enum.Font.GothamMedium
	text.TextXAlignment = Enum.TextXAlignment.Left
	text.TextYAlignment = Enum.TextYAlignment.Center
	text.TextWrapped = true
	text.ZIndex = 301
	text.Parent = textContainer
	if statusCode then
		local statusBadge = Instance.new("Frame")
		statusBadge.Name = "StatusBadge"
		statusBadge.Size = UDim2.new(0, 44, 0, 28)
		statusBadge.Position = UDim2.new(1, -12, 0.5, 0)
		statusBadge.AnchorPoint = Vector2.new(1, 0.5)
		statusBadge.BackgroundColor3 = toastColor
		statusBadge.BackgroundTransparency = 0.8
		statusBadge.BorderSizePixel = 0
		statusBadge.ZIndex = 301
		statusBadge.Parent = toast
		Utils.Round(statusBadge, 8)
		Utils.CreateStroke(statusBadge, toastColor, 1, Configuration.BorderTransparency)
		local statusCodeLabel = Instance.new("TextLabel")
		statusCodeLabel.Name = "StatusCode"
		statusCodeLabel.Size = UDim2.new(1, 0, 1, 0)
		statusCodeLabel.BackgroundTransparency = 1
		statusCodeLabel.Text = tostring(statusCode)
		statusCodeLabel.TextColor3 = toastColor
		statusCodeLabel.TextSize = Configuration.Fonts.Small
		statusCodeLabel.Font = Enum.Font.GothamBold
		statusCodeLabel.ZIndex = 302
		statusCodeLabel.Parent = statusBadge
	end
	table.insert(ToastSystem.ActiveToasts, toast)
	ToastSystem.RepositionToasts()
	local targetWidth = 320
	Utils.TweenBack(toast, {Size = UDim2.new(0, targetWidth, 0, toastHeight)}, Configuration.Animations.Medium)
	task.delay(
		duration or 3.5,
		function()
			if toast.Parent then
				Utils.Tween(
					toast,
					{
						Position = UDim2.new(0.5, 0, 0, -80),
						BackgroundTransparency = 1
					},
					Configuration.Animations.Medium
				)
				for i, t in ipairs(ToastSystem.ActiveToasts) do
					if t == toast then
						table.remove(ToastSystem.ActiveToasts, i)
						break
					end
				end
				task.wait(Configuration.Animations.Medium)
				toast:Destroy()
				ToastSystem.RepositionToasts()
			end
		end
	)
	return toast
end

ToastSystem.RepositionToasts = function()
	for i, toast in ipairs(ToastSystem.ActiveToasts) do
		local targetY = 20 + ((i - 1) * (60 + ToastSystem.ToastSpacing))
		Utils.Tween(toast, {Position = UDim2.new(0.5, 0, 0, targetY)}, Configuration.Animations.Medium)
	end
end

local function Build()
	local parent = game:GetService("CoreGui")
	local old = parent:FindFirstChild(Configuration.ScreenGuiName)
	if old then
		old:Destroy()
	end
	local screen = Instance.new("ScreenGui")
	screen.Name = Configuration.ScreenGuiName
	screen.ResetOnSpawn = false
	screen.Parent = parent

	-- Discord banner (top of screen, transparent, blinking + glow)
	local discordBanner = Instance.new("TextLabel")
	discordBanner.Name = "DiscordBanner"
	discordBanner.Size = UDim2.new(0, 400, 0, 32)
	discordBanner.Position = UDim2.new(0.5, 0, 0, 10)
	discordBanner.AnchorPoint = Vector2.new(0.5, 0)
	discordBanner.BackgroundTransparency = 1
	discordBanner.Text = "Join https://discord.gg/EFFKrfFkPQ"
	discordBanner.TextColor3 = Color3.fromRGB(88, 101, 242)
	discordBanner.TextSize = 16
	discordBanner.Font = Enum.Font.GothamBold
	discordBanner.TextTransparency = 0
	discordBanner.Parent = screen

	local bannerStroke = Instance.new("UIStroke")
	bannerStroke.Color = Color3.fromRGB(88, 101, 242)
	bannerStroke.Thickness = 2
	bannerStroke.Transparency = 0.3
	bannerStroke.Parent = discordBanner

	task.spawn(function()
		while discordBanner and discordBanner.Parent do
			Utils.Tween(discordBanner, {TextTransparency = 0.4}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.7}, 0.6)
			task.wait(0.6)
			Utils.Tween(discordBanner, {TextTransparency = 0}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.3}, 0.6)
			task.wait(0.6)
		end
	end)

	local overlay = Instance.new("Frame")
	overlay.Size = UDim2.fromScale(1, 1)
	overlay.BackgroundColor3 = Color3.new(0, 0, 0)
	overlay.BackgroundTransparency = 1
	overlay.Parent = screen
	Utils.Tween(overlay, {BackgroundTransparency = 1}, 1)
	SetBlur(true)
	local main = Instance.new("Frame")
	main.Size = Configuration.Window.Size
	main.Position = UDim2.new(0.5, 0, 0.5, 60)
	main.AnchorPoint = Vector2.new(0.5, 0.5)
	main.BackgroundColor3 = Configuration.Colors.Bg
	main.BackgroundTransparency = 0.2
	main.ClipsDescendants = true
	main.Parent = screen
	Utils.Round(main, 24)
	Utils.Stroke(main, Color3.new(1, 1, 1), 1, 0.92)
	local glass = Instance.new("Frame")
	glass.Size = UDim2.fromScale(1, 1)
	glass.BackgroundColor3 = Color3.new(1, 1, 1)
	glass.BackgroundTransparency = 0.985
	glass.ZIndex = 0
	glass.Parent = main
	Utils.Round(glass, 24)
	local bar = Instance.new("Frame")
	bar.Size = UDim2.new(1, 0, 0, 54)
	bar.BackgroundTransparency = 1
	bar.Parent = main
	local dots = Instance.new("Frame")
	dots.Size = UDim2.new(0, 54, 0, 12)
	dots.Position = UDim2.new(0, 20, 0.5, 0)
	dots.AnchorPoint = Vector2.new(0, 0.5)
	dots.BackgroundTransparency = 1
	dots.Parent = bar
	local dColors = {
		Configuration.Colors.TrafficRed,
		Configuration.Colors.TrafficYellow,
		Configuration.Colors.TrafficGreen
	}
	for i, c in ipairs(dColors) do
		local d = Instance.new("Frame")
		d.Size = UDim2.fromOffset(12, 12)
		d.Position = UDim2.fromOffset((i - 1) * 18, 0)
		d.BackgroundColor3 = c
		d.BorderSizePixel = 0
		d.Parent = dots
		Utils.Round(d, 6)
	end
	local titleText = Instance.new("TextLabel")
	titleText.Size = UDim2.new(1, 0, 1, 0)
	titleText.Text = "JUNKIE"
	titleText.TextColor3 = Color3.new(1, 1, 1)
	titleText.TextTransparency = 0.7
	titleText.TextSize = 10
	titleText.Font = Enum.Font.GothamBold
	titleText.BackgroundTransparency = 1
	titleText.Parent = bar
	local content = Instance.new("ScrollingFrame")
	content.Size = UDim2.new(1, 0, 1, -54)
	content.Position = UDim2.new(0, 0, 0, 54)
	content.BackgroundTransparency = 1
	content.ScrollBarThickness = 0
	content.CanvasSize = UDim2.new(0, 0, 0, 440)
	content.Parent = main
	local list = Instance.new("UIListLayout")
	list.Padding = UDim.new(0, 24)
	list.HorizontalAlignment = Enum.HorizontalAlignment.Center
	list.Parent = content
	local pad = Instance.new("UIPadding")
	pad.PaddingTop = UDim.new(0, 5)
	pad.Parent = content
	local logoContainer = Instance.new("Frame")
	logoContainer.Size = UDim2.fromOffset(80, 80)
	logoContainer.BackgroundColor3 = Configuration.Colors.Primary
	logoContainer.Parent = content
	Utils.Round(logoContainer, 20)
	local grad = Instance.new("UIGradient")
	grad.Color = ColorSequence.new(Configuration.Colors.Primary, Configuration.Colors.PrimaryDark)
	grad.Rotation = 45
	grad.Parent = logoContainer
	local sIcon = Instance.new("ImageLabel")
	sIcon.Size = UDim2.fromScale(1, 1)
	sIcon.Position = UDim2.fromScale(0.5, 0.5)
	sIcon.AnchorPoint = Vector2.new(0.5, 0.5)
	sIcon.Image = Icons.JunkieNewIcon
	sIcon.ScaleType = Enum.ScaleType.Fit
	sIcon.BackgroundTransparency = 1
	sIcon.Parent = logoContainer
	local titleArea = Instance.new("Frame")
	titleArea.Size = UDim2.new(1, 0, 0, 44)
	titleArea.BackgroundTransparency = 1
	titleArea.Parent = content
	local mainTitle = Instance.new("TextLabel")
	mainTitle.Size = UDim2.new(1, 0, 0, 26)
	mainTitle.Text = "Junkie"
	mainTitle.TextColor3 = Color3.new(1, 1, 1)
	mainTitle.TextSize = 26
	mainTitle.Font = Enum.Font.GothamBold
	mainTitle.BackgroundTransparency = 1
	mainTitle.Parent = titleArea
	local subTitle = Instance.new("TextLabel")
	subTitle.Size = UDim2.new(1, 0, 0, 16)
	subTitle.Position = UDim2.fromOffset(0, 28)
	subTitle.Text = "junkie-development.de"
	subTitle.TextColor3 = Configuration.Colors.TextSec
	subTitle.TextSize = 13
	subTitle.Font = Enum.Font.Gotham
	subTitle.BackgroundTransparency = 1
	subTitle.Parent = titleArea
	local statusCard = Instance.new("Frame")
	statusCard.Size = UDim2.new(0, 280, 0, 68)
	statusCard.BackgroundColor3 = Color3.new(1, 1, 1)
	statusCard.BackgroundTransparency = 0.96
	statusCard.Parent = content
	Utils.Round(statusCard, 16)
	local sStroke = Utils.Stroke(statusCard, Color3.new(1, 1, 1), 1, 0.95)
	local sIconBg = Instance.new("Frame")
	sIconBg.Size = UDim2.fromOffset(42, 42)
	sIconBg.Position = UDim2.new(0, 14, 0.5, 0)
	sIconBg.AnchorPoint = Vector2.new(0, 0.5)
	sIconBg.BackgroundColor3 = Configuration.Colors.StatusIdle
	sIconBg.BackgroundTransparency = 0.9
	sIconBg.Parent = statusCard
	Utils.Round(sIconBg, 21)
	local sImg = Instance.new("ImageLabel")
	sImg.Size = UDim2.fromScale(0.5, 0.5)
	sImg.Position = UDim2.fromScale(0.5, 0.5)
	sImg.AnchorPoint = Vector2.new(0.5, 0.5)
	sImg.Image = Icons.Lock
	sImg.ImageColor3 = Configuration.Colors.StatusIdle
	sImg.BackgroundTransparency = 1
	sImg.Parent = sIconBg
	local sLabel = Instance.new("TextLabel")
	sLabel.Size = UDim2.new(1, -70, 0, 14)
	sLabel.Position = UDim2.fromOffset(70, 16)
	sLabel.Text = "CURRENT STATUS"
	sLabel.TextColor3 = Configuration.Colors.TextMuted
	sLabel.TextSize = 10
	sLabel.Font = Enum.Font.GothamBold
	sLabel.TextXAlignment = Enum.TextXAlignment.Left
	sLabel.BackgroundTransparency = 1
	sLabel.Parent = statusCard
	local sValue = Instance.new("TextLabel")
	sValue.Size = UDim2.new(1, -70, 0, 20)
	sValue.Position = UDim2.fromOffset(70, 32)
	sValue.Text = "No key detected"
	sValue.TextColor3 = Configuration.Colors.StatusIdle
	sValue.TextSize = 15
	sValue.Font = Enum.Font.GothamMedium
	sValue.TextXAlignment = Enum.TextXAlignment.Left
	sValue.BackgroundTransparency = 1
	sValue.Parent = statusCard
	local inputFrame = Instance.new("Frame")
	inputFrame.Size = UDim2.new(0, 280, 0, 52)
	inputFrame.BackgroundColor3 = Color3.new(1, 1, 1)
	inputFrame.BackgroundTransparency = 0.975
	inputFrame.Parent = content
	Utils.Round(inputFrame, 14)
	local iStroke = Utils.Stroke(inputFrame, Color3.new(1, 1, 1), 1, 0.95)
	local kIcon = Instance.new("ImageLabel")
	kIcon.Size = UDim2.fromOffset(18, 18)
	kIcon.Position = UDim2.new(0, 14, 0.5, 0)
	kIcon.AnchorPoint = Vector2.new(0, 0.5)
	kIcon.Image = Icons.Key
	kIcon.ImageColor3 = Configuration.Colors.TextMuted
	kIcon.BackgroundTransparency = 1
	kIcon.Parent = inputFrame
	local box = Instance.new("TextBox")
	box.Size = UDim2.new(1, -85, 1, 0)
	box.Position = UDim2.fromOffset(45, 0)
	box.Text = ""
	box.PlaceholderText = "Enter your key..."
	box.TextColor3 = Color3.new(1, 1, 1)
	box.TextSize = 14
	box.Font = Enum.Font.Gotham
	box.BackgroundTransparency = 1
	box.TextXAlignment = Enum.TextXAlignment.Left
	box.Parent = inputFrame
	local paste = Instance.new("ImageButton")
	paste.Size = UDim2.fromOffset(18, 18)
	paste.Position = UDim2.new(1, -14, 0.5, 0)
	paste.AnchorPoint = Vector2.new(1, 0.5)
	paste.Image = Icons.Copy
	paste.ImageColor3 = Configuration.Colors.TextMuted
	paste.BackgroundTransparency = 1
	paste.Parent = inputFrame
	local btnRow = Instance.new("Frame")
	btnRow.Size = UDim2.new(0, 280, 0, 50)
	btnRow.BackgroundTransparency = 1
	btnRow.Parent = content
	local redeem = Instance.new("TextButton")
	redeem.Size = UDim2.new(0.5, -8, 1, 0)
	redeem.BackgroundColor3 = Configuration.Colors.Primary
	redeem.Text = "Redeem"
	redeem.TextColor3 = Color3.new(1, 1, 1)
	redeem.Font = Enum.Font.GothamBold
	redeem.TextSize = 14
	redeem.AutoButtonColor = false
	redeem.Parent = btnRow
	Utils.Round(redeem, 14)
	local getKey = Instance.new("TextButton")
	getKey.Size = UDim2.new(0.5, -8, 1, 0)
	getKey.Position = UDim2.new(0.5, 8, 0, 0)
	getKey.BackgroundColor3 = Color3.new(1, 1, 1)
	getKey.BackgroundTransparency = 0.955
	getKey.Text = "Get Key"
	getKey.TextColor3 = Color3.new(1, 1, 1)
	getKey.Font = Enum.Font.GothamBold
	getKey.TextSize = 14
	getKey.AutoButtonColor = false
	getKey.Parent = btnRow
	Utils.Round(getKey, 14)
	Utils.Stroke(getKey, Color3.new(1, 1, 1), 1, 0.94)
	local function ApplyHover(btn)
		local baseColor = btn.BackgroundColor3
		btn.MouseEnter:Connect(
			function()
				Utils.Tween(
					btn,
					{
						BackgroundColor3 = baseColor:Lerp(Color3.new(1, 1, 1), 0.1)
					},
					0.2
				)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset + 4, btn.Size.Y.Scale, btn.Size.Y.Offset + 2)
					},
					0.2
				)
			end
		)
		btn.MouseLeave:Connect(
			function()
				Utils.Tween(btn, {BackgroundColor3 = baseColor}, 0.2)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset - 4, btn.Size.Y.Scale, btn.Size.Y.Offset - 2)
					},
					0.2
				)
			end
		)
	end
	ApplyHover(redeem)
	ApplyHover(getKey)
	box.Focused:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.5, Thickness = 1.2}, 0.3)
		end
	)
	box.FocusLost:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.95, Thickness = 1}, 0.3)
		end
	)
	local spinConnection
	local dotsThread
	local function SetStatus(state)
		if spinConnection then
			spinConnection:Disconnect()
			spinConnection = nil
			sImg.Rotation = 0
		end
		if dotsThread then
			task.cancel(dotsThread)
			dotsThread = nil
		end
		local color = Configuration.Colors.StatusIdle
		local icon = Icons.Lock
		local text = "No key detected"
		if state == "verifying" then
			color = Configuration.Colors.StatusVerifying
			icon = Icons.Loading
			text = "Verifying access"
			spinConnection =
				RunService.Heartbeat:Connect(
				function(dt)
					if not sImg or not sImg.Parent then
						if spinConnection then
							spinConnection:Disconnect()
						end
						spinConnection = nil
						return
					end
					sImg.Rotation = (sImg.Rotation + dt * 360) % 360
				end
			)
			local dots = {".", "..", "...", ""}
			local i = 1
			dotsThread =
				task.spawn(
				function()
					while sValue and sValue.Parent do
						if not sValue.Text:find("Verifying access", 1, true) then
							break
						end
						sValue.Text = text .. dots[i]
						i = (i % #dots) + 1
						task.wait(0.45)
					end
				end
			)
		elseif state == "success" then
			color = Configuration.Colors.StatusSuccess
			icon = Icons.CheckCircle
			text = "Access Granted"
		elseif state == "error" then
			color = Configuration.Colors.StatusError
			icon = Icons.XCircle
			text = "Invalid Key"
		end
		Utils.Tween(sValue, {TextColor3 = color}, 0.35)
		Utils.Tween(sImg, {ImageColor3 = color}, 0.35)
		Utils.Tween(sIconBg, {BackgroundColor3 = color}, 0.35)
		sValue.Text = text
		sImg.Image = icon
	end
	redeem.MouseButton1Click:Connect(
		function()
			local key = (box.Text:gsub("%s+", "")) -- trim spaces; keep case (work.ink tokens are lowercase)
			SetStatus("verifying")
			redeem.Text = "..."
			redeem.Active = false
            local result = Junkie.check_key(key)
			redeem.Active = true
			redeem.Text = "Redeem"
			if not result then
				SetStatus("error")
				ToastSystem.Create(screen, "API request failed: " .. tostring(result), "error")
				return
			end
			if result.valid then
                saveVerifiedKey(key)
                getgenv().SCRIPT_KEY = key
                SetStatus("success")
                ToastSystem.Create(screen, "Access granted!", "success", nil, status)
                task.wait(0.8)
                SetBlur(false)
                Utils.Tween(
                    main,
                    {
                        Position = UDim2.new(0.5, 0, 0.5, 100),
                        BackgroundTransparency = 1
                    },
                    0.7,
                    Enum.EasingStyle.Exponential,
                    Enum.EasingDirection.In
                )
                task.delay(
                    0.7,
                    function()
                        screen:Destroy()
                    end
                )
			else
				SetStatus("error")
				ToastSystem.Create(screen, result.message or "Invalid key", "error", nil, status)
			end
		end
	)
	getKey.MouseButton1Click:Connect(
		function()
			setclipboard(Junkie.get_key_link())
			ToastSystem.Create(screen, "Key link has been copied to clipboard", "success")
		end
	)
	paste.MouseButton1Click:Connect(
		function()
			ToastSystem.Create(screen, "Paste functionality not supported in Roblox (security reasons)", "warning")
		end
	)
	main.Position = UDim2.new(0.5, 0, 0.5, 100)
	main.BackgroundTransparency = 1
	Utils.Tween(
		main,
		{
			Position = UDim2.new(0.5, 0, 0.5, 0),
			BackgroundTransparency = 0.2
		},
		1,
		Enum.EasingStyle.Exponential
	)
	local dragging, dragStart, startPos
	bar.InputBegan:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = true
				dragStart = input.Position
				startPos = main.Position
			end
		end
	)
	UserInputService.InputChanged:Connect(
		function(input)
			if dragging and input.UserInputType == Enum.UserInputType.MouseMovement then
				local delta = input.Position - dragStart
				main.Position =
					UDim2.new(startPos.X.Scale, startPos.X.Offset + delta.X, startPos.Y.Scale, startPos.Y.Offset + delta.Y)
			end
		end
	)
	UserInputService.InputEnded:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = false
			end
		end
	)
	return screen
end

local savedKey = loadVerifiedKey()
local keyToCheck = savedKey
if not keyToCheck then
    keyToCheck = getgenv().SCRIPT_KEY
end

local result = Junkie.check_key(keyToCheck)
if result and result.valid then
    if result.message == "KEYLESS" then
        getgenv().SCRIPT_KEY = "KEYLESS"
    elseif result.message == "KEY_VALID" then
        if not savedKey and keyToCheck then
            saveVerifiedKey(keyToCheck)
        end
        getgenv().SCRIPT_KEY = keyToCheck
    else
        Build()
    end
else
    Build()
end

while not getgenv().SCRIPT_KEY do
    task.wait(0.1)
end
end
__y2k_keygate()
-- ===== Protected payload =====
-- Protected with Vm runtime. Tampering halts execution.
-- Vm protection runtime (bundled). Do not edit by hand.
local Crypt = (function()
--!nonstrict
-- ============================================================================
--  Crypt.lua  --  lightweight obfuscation / integrity primitives
--  Part of the Vm protection runtime. No external deps. Luau-safe.
--
--  Provides: XOR string cipher, FNV-1a hash, base64, and a small PRNG so the
--  runtime can hide embedded strings (URLs, function names) and verify
--  integrity without leaving plaintext secrets in the bytecode.
-- ============================================================================

local Crypt = {}

local schar, sbyte, ssub, srep = string.char, string.byte, string.sub, string.rep
local tconcat = table.concat
local bxor = bit32 and bit32.bxor or function(a, b)
	local r, p = 0, 1
	while a > 0 or b > 0 do
		local x, y = a % 2, b % 2
		if x ~= y then r = r + p end
		a, b, p = (a - x) / 2, (b - y) / 2, p * 2
	end
	return r
end

-- 32-bit multiply mod 2^32 that stays within double precision (2^53).
-- Splitting the accumulator into hi/lo 16-bit halves keeps every intermediate
-- product under 2^42, so no precision is lost (a plain h*16777619 overflows 2^53).
local function mul32(a, b)
	local ah = (a - a % 65536) / 65536   -- floor(a / 2^16), < 2^16
	local al = a % 65536                  -- a mod 2^16, < 2^16
	return ((ah * b % 65536) * 65536 + al * b) % 4294967296
end

-- FNV-1a 32-bit hash of a string (used for integrity fingerprints)
function Crypt.hash(s)
	local h = 2166136261
	for i = 1, #s do
		h = bxor(h, sbyte(s, i))
		h = mul32(h, 16777619)
	end
	return h
end

-- repeating-key XOR cipher (symmetric). key is a string.
function Crypt.xor(data, key)
	local out, kl = {}, #key
	for i = 1, #data do
		out[i] = schar(bxor(sbyte(data, i), sbyte(key, (i - 1) % kl + 1)))
	end
	return tconcat(out)
end

-- deterministic PRNG (xorshift) seeded from a string; for shuffling/jitter
function Crypt.rng(seed)
	local state = (type(seed) == "string") and Crypt.hash(seed) or (seed or 0x1234567)
	if state == 0 then state = 0x9E3779B9 end
	return function()
		state = bxor(state, (state * 32) % 4294967296)
		state = bxor(state, math.floor(state / 8))
		state = bxor(state, (state * 16384) % 4294967296)
		state = state % 4294967296
		return state / 4294967296
	end
end

-- base64 (so ciphertext survives as a string literal in the bundle)
local B64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
function Crypt.b64encode(data)
	local out = {}
	for i = 1, #data, 3 do
		local a, b, c = sbyte(data, i), sbyte(data, i + 1), sbyte(data, i + 2)
		local n = a * 65536 + (b or 0) * 256 + (c or 0)
		local c1 = math.floor(n / 262144) % 64
		local c2 = math.floor(n / 4096) % 64
		local c3 = math.floor(n / 64) % 64
		local c4 = n % 64
		out[#out + 1] = ssub(B64, c1 + 1, c1 + 1)
		out[#out + 1] = ssub(B64, c2 + 1, c2 + 1)
		out[#out + 1] = b and ssub(B64, c3 + 1, c3 + 1) or "="
		out[#out + 1] = c and ssub(B64, c4 + 1, c4 + 1) or "="
	end
	return tconcat(out)
end

local B64I
function Crypt.b64decode(data)
	if not B64I then
		B64I = {}
		for i = 1, #B64 do B64I[ssub(B64, i, i)] = i - 1 end
	end
	data = string.gsub(data, "[^" .. B64 .. "]", "")
	local out = {}
	for i = 1, #data, 4 do
		local a = B64I[ssub(data, i, i)] or 0
		local b = B64I[ssub(data, i + 1, i + 1)] or 0
		local c = B64I[ssub(data, i + 2, i + 2)]
		local d = B64I[ssub(data, i + 3, i + 3)]
		local n = a * 262144 + b * 4096 + (c or 0) * 64 + (d or 0)
		out[#out + 1] = schar(math.floor(n / 65536) % 256)
		if c then out[#out + 1] = schar(math.floor(n / 256) % 256) end
		if d then out[#out + 1] = schar(n % 256) end
	end
	return tconcat(out)
end

-- convenience: encrypt a plaintext to a portable token (b64(xor(data,key)))
function Crypt.seal(plaintext, key)
	return Crypt.b64encode(Crypt.xor(plaintext, key))
end
function Crypt.open(token, key)
	return Crypt.xor(Crypt.b64decode(token), key)
end

return Crypt

end)()
local Secure = (function()
--!nonstrict
-- ============================================================================
--  Secure.lua  --  capture real executor functions & expose protected proxies
--
--  THE CORE PROTECTION. At load time (before any spy can install hooks) we grab
--  references to the real executor functions into PRIVATE upvalues, then hand
--  the wrapped script only thin proxies. Because the proxies call the captured
--  originals directly, a spy that later hooks the GLOBAL `request` / `http` /
--  `readfile` never sees the script's calls -- they bypass the global.
--
--  Proxies are wrapped with newcclosure so they read as native C-closures:
--  iscclosure() passes, and getupvalues() is blocked on them by most executors,
--  hiding the captured originals from getgc/upvalue inspection.
-- ============================================================================

local Secure = {}

-- resolve the real global table as early as possible
local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local rawget, rawset = rawget, rawset
local iscc = iscclosure
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction or function(f) return f end

-- list of sensitive globals we proxy. (function-valued globals only)
local CAPTURE = {
	"request", "http_request", "readfile", "writefile", "appendfile", "isfile",
	"isfolder", "listfiles", "makefolder", "delfile", "delfolder", "loadstring",
	"getgenv", "getrawmetatable", "setrawmetatable", "hookfunction", "hookmetamethod",
	"newcclosure", "getnamecallmethod", "setclipboard", "queue_on_teleport",
	"getcustomasset", "fireclickdetector", "firetouchinterest", "fireproximityprompt",
	"isexecutorclosure", "checkcaller", "getconnections", "getcallingscript",
}

-- Capture the real functions. Returns a PRIVATE table (kept as an upvalue by the
-- caller -- never store this in a global).
function Secure.capture()
	local raw = {}

	-- http via the common executor spellings, in priority order
	raw.http = (syn and syn.request) or (http and http.request) or http_request or request
	-- guard: if http appears already hooked (became an l-closure), remember it
	raw.http_tampered = (iscc and raw.http and not iscc(raw.http)) or false

	for _, name in ipairs(CAPTURE) do
		local fn = rawget(realG, name)
		if type(fn) == "function" then
			-- clone where supported so even a later identity-swap of the global
			-- can't reach our reference
			local ok, c = pcall(clonef, fn)
			raw[name] = ok and c or fn
			raw[name .. "_genuine"] = (iscc and iscc(fn)) or false
		end
	end

	-- HttpGet/HttpGetAsync live on `game`; capture bound callers
	local okGame = pcall(function() return game and game.HttpGet end)
	if okGame and game then
		raw.HttpGet = function(url, ...) return game:HttpGet(url, ...) end
		raw.HttpGetAsync = function(url, ...) return game:HttpGetAsync(url, ...) end
	end

	return raw
end

-- Build the proxy table the sandbox exposes. `raw` is the private capture.
-- Each proxy is a newcclosure so its upvalues (the real fn) are not inspectable.
function Secure.proxies(raw)
	local P = {}

	local function wrap(realFn)
		if type(realFn) ~= "function" then return nil end
		return newcc(function(...) return realFn(...) end)
	end

	-- generic passthrough proxies
	for _, name in ipairs(CAPTURE) do
		if raw[name] then P[name] = wrap(raw[name]) end
	end

	-- unified HTTP proxy (the prime spy target). Accepts the standard {Url=...}.
	if raw.http then
		local http = raw.http
		P.request = newcc(function(opts) return http(opts) end)
		P.http_request = P.request
		if syn then P.syn = { request = P.request } end
	end
	if raw.HttpGet then
		P.HttpGet = newcc(function(url, ...) return raw.HttpGet(url, ...) end)
		P.HttpGetAsync = newcc(function(url, ...) return raw.HttpGetAsync(url, ...) end)
	end

	return P
end

-- Snapshot identities so Integrity can detect later replacement of our proxies.
function Secure.fingerprint(P)
	local fp = {}
	for k, v in pairs(P) do
		if type(v) == "function" then fp[k] = v end
	end
	return fp
end

return Secure

end)()
local Environment = (function()
--!nonstrict
-- ============================================================================
--  Environment.lua  --  the sealed sandbox the wrapped script runs inside
--
--  Builds a custom _ENV whose:
--    * function-valued executor globals resolve to PROTECTED PROXIES
--    * everything else falls through to the real globals (so game, workspace,
--      Instance, math, string, task, etc. all work -- full Luau semantics)
--    * writes stay local to the sandbox (script can't pollute real _G)
--    * the metatable is private (Integrity verifies it wasn't swapped)
--
--  This is the isolation layer: the script believes it has a normal global
--  environment, but its sensitive calls are routed through the Vm.
-- ============================================================================

local Environment = {}

function Environment.build(proxies, realG)
	realG = realG or (getgenv and getgenv()) or _G

	-- the sandbox's own storage for globals the script defines
	local store = {}

	-- private metatable (kept out of the sandbox; Integrity holds a ref)
	local mt = {}

	mt.__index = function(_, key)
		-- 1. protected proxy?
		local p = proxies[key]
		if p ~= nil then return p end
		-- 2. script-local global?
		local s = store[key]
		if s ~= nil then return s end
		-- 3. fall through to the real environment
		return realG[key]
	end

	mt.__newindex = function(_, key, value)
		-- keep all writes inside the sandbox (never touch real globals)
		store[key] = value
	end

	-- unique private lock token. __metatable makes getmetatable(env) return THIS
	-- (hiding the real mt) and makes setmetatable(env, ...) error -- so the env's
	-- metatable cannot be swapped. Integrity verifies this token is still in place.
	local lock = {}
	mt.__metatable = lock

	local env = setmetatable({}, mt)

	-- expose a sandboxed getfenv/getgenv so the script's own introspection
	-- returns the sandbox, not the real globals (don't leak the boundary)
	store.getgenv = function() return env end
	store._G = env
	store.shared = store.shared or {}

	return env, mt, store, lock
end

return Environment

end)()
local Integrity = (function()
--!nonstrict
-- ============================================================================
--  Integrity.lua  --  anti-tamper / anti-penetration
--
--  Verifies the runtime hasn't been hooked or swapped, both at startup and via
--  a background watchdog. On tamper it triggers a caller-supplied onTamper
--  (the Vm wipes the sandbox + halts).
--
--  Checks:
--   * capture genuineness   -- were the executor funcs already hooked at capture?
--   * proxy identity         -- have our proxies been replaced since fingerprint?
--   * env seal               -- is the sandbox __index/__newindex intact?
--   * hostile introspection  -- is something actively decompiling/hooking us?
--   * source checksum        -- does the protected payload still match?
-- ============================================================================

local Integrity = {}

local iscc = iscclosure
local getus = getupvalues or (debug and debug.getupvalues)

-- 1. Were any captured executor functions already hooks (l-closures) at capture?
function Integrity.checkCapture(raw)
	local suspicious = {}
	if raw.http_tampered then suspicious[#suspicious + 1] = "http" end
	for k, v in pairs(raw) do
		if string.sub(k, -8) == "_genuine" and v == false then
			suspicious[#suspicious + 1] = string.sub(k, 1, -9)
		end
	end
	return suspicious
end

-- 2. Our proxies must still be the exact functions we created.
function Integrity.checkProxies(P, fingerprint)
	for k, original in pairs(fingerprint) do
		if P[k] ~= original then return false, k end
	end
	return true
end

-- 3. The sandbox env metatable must be intact (not re-pointed to leak globals).
function Integrity.checkEnv(env, expectedMT)
	local mt = getmetatable(env)
	if mt ~= expectedMT then return false, "metatable" end
	return true
end

-- 4. Best-effort: detect if our own proxies have become inspectable (a sign a
--    de-hook tool unwrapped the cclosure). On a healthy executor getupvalues on
--    a newcclosure should be empty/blocked; non-empty => someone unwrapped it.
function Integrity.checkOpaque(P)
	if not getus then return true end
	for _, v in pairs(P) do
		if type(v) == "function" then
			local ok, ups = pcall(getus, v)
			if ok and type(ups) == "table" and next(ups) ~= nil then
				return false
			end
		end
	end
	return true
end

-- run all startup checks; returns ok, reason
function Integrity.startup(ctx)
	local sus = Integrity.checkCapture(ctx.raw)
	if #sus > 0 and ctx.strict then
		return false, "capture-hooked:" .. table.concat(sus, ",")
	end
	local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
	if not okP then return false, "proxy-swapped:" .. tostring(badKey) end
	local okE, why = Integrity.checkEnv(ctx.env, ctx.envLock)
	if not okE then return false, "env-" .. tostring(why) end
	if not Integrity.checkOpaque(ctx.proxies) then return false, "opaque-broken" end
	return true
end

-- background watchdog: re-run cheap checks on an interval and self-destruct.
-- Spawns through the Memory scope (ctx.mem) so the thread is tracked and
-- cancelled on cleanup -- it can never leak past the script's lifetime.
function Integrity.watchdog(ctx, onTamper)
	local wait_ = (task and task.wait) or wait
	local body = function()
		while ctx.alive do
			wait_(ctx.interval or 2)
			if not ctx.alive then return end
			local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
			local okE = Integrity.checkEnv(ctx.env, ctx.envLock)
			if not okP or not okE then
				ctx.alive = false
				pcall(onTamper, okP and "env" or ("proxy:" .. tostring(badKey)))
				return
			end
		end
	end
	if ctx.mem and ctx.mem.spawn then
		ctx.mem:spawn(body)
	else
		local spawn = (task and task.spawn) or spawn
		if spawn then spawn(body) end
	end
end

return Integrity

end)()
local Stealth = (function()
--!nonstrict
-- ============================================================================
--  Stealth.lua  --  comprehensive environment spoofing / anti-detection
--
--  Covers the full sUNC executor surface (docs.sunc.su). For each function an
--  anti-cheat could use to fingerprint the executor, detect hooks, or scan for
--  injected objects, we install a fake that answers "clean" -- while leaving the
--  function usable for everyone else.
--
--  Technique: hookfunction (rewrites the function OBJECT, so even a reference
--  the AC captured early is affected), replacement wrapped in newcclosure (stays
--  a C-closure -> passes iscclosure). Everything pcall-guarded; only spoofs what
--  the executor actually exposes.
--
--  HONEST: beats ACs that read these globals at runtime and trust them. Does NOT
--  beat an AC that ran fully before you, re-implements checks in its own VM, or
--  validates server-side. Raises the bar across games.
-- ============================================================================

local Stealth = {}

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction
local hookf = hookfunction
local cloneref_ = cloneref or function(x) return x end
local rawget, rawset = rawget, rawset

-- private registries (weak so we never pin objects alive)
local hiddenObjs = setmetatable({}, { __mode = "k" })  -- hide from gc/instance scans
local genuineFns = setmetatable({}, { __mode = "k" })  -- report as un-hooked / ours
local ourScripts = setmetatable({}, { __mode = "k" })  -- hide script bytecode/closure
local installed  = false

function Stealth.hide(o)        if o ~= nil then hiddenObjs[o] = true end return o end
function Stealth.markGenuine(f) if type(f) == "function" then genuineFns[f] = true end return f end
function Stealth.hideScript(s)  if s ~= nil then ourScripts[s] = true end return s end

-- ---- hook helpers ---------------------------------------------------------
-- CRITICAL: after hookfunction(real, repl), the `real` OBJECT behaves like repl.
-- So the replacement must NOT call `real` on its passthrough path (that would be
-- infinite recursion -> C stack overflow). We clone the original FIRST and have
-- the replacement call the unhooked clone. If we can't clone, we fall back to a
-- plain global swap (which leaves `real` itself untouched, so calling it is safe).
local function emplace(container, name, build)
	if type(container) ~= "table" then return end
	local real = rawget(container, name)
	if type(real) ~= "function" then return end
	if hookf and clonef then
		local okc, orig = pcall(clonef, real)
		if okc and type(orig) == "function" then
			local repl = newcc(build(orig))         -- repl -> clone (unhooked): safe
			genuineFns[repl] = true; hiddenObjs[repl] = true
			if pcall(hookf, real, repl) then return end
		end
	end
	-- fallback: global/table swap, repl -> real (real is NOT hooked here): safe
	local repl = newcc(build(real))
	genuineFns[repl] = true; hiddenObjs[repl] = true
	pcall(rawset, container, name, repl)
end

local function spoof(name, build)            emplace(realG, name, build) end
local function spoofIn(tbl, name, build)     emplace(tbl, name, build) end

-- filter our hidden/genuine objects out of an array-like result table.
local function filterArray(t)
	if type(t) ~= "table" then return t end
	local out = {}
	for i = 1, #t do
		local v = t[i]
		if not (hiddenObjs[v] or genuineFns[v]) then out[#out + 1] = v end
	end
	return out
end

-- ===========================================================================
function Stealth.install(opts)
	if installed then return end
	installed = true
	opts = opts or {}
	local fakeName = opts.spoofName            -- nil => "no executor"
	local fakeVer  = opts.spoofVersion or "1.0.0"

	-- DISGUISE: a real game LocalScript (cloneref'd) to report as the "calling
	-- script", so introspection sees a legit script instead of getcallingscript()
	-- == nil (which screams "injected"). On by default; opts.disguise=false to skip.
	local decoyScript = nil
	if opts.disguise ~= false then
		pcall(function()
			local lp = game:GetService("Players").LocalPlayer
			local char = lp and lp.Character
			decoyScript = (char and char:FindFirstChild("Animate"))
				or (lp and lp:FindFirstChildWhichIsA("LocalScript", true))
		end)
		if decoyScript then pcall(function() decoyScript = cloneref_(decoyScript) end) end
	end

	-- 1) IDENTITY ----------------------------------------------------------
	for _, n in ipairs({ "identifyexecutor", "getexecutorname", "iexecutor" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end

	-- 2) CLOSURE CHECKS ----------------------------------------------------
	spoof("iscclosure",       function(r) return function(f) if genuineFns[f] then return true  end return r(f) end end)
	spoof("isexecutorclosure",function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("isourclosure",     function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("islclosure",       function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("checkcaller",      function(r) return function() return false end end)
	-- stable fake hash for our funcs so repeated checks stay consistent
	spoof("getfunctionhash",  function(r) return function(f) if genuineFns[f] then return "00000000000000000000000000000000" end return r(f) end end)

	-- 3) ENVIRONMENT / GC scans -- strip our objects ----------------------
	spoof("getgc",     function(r) return function(...) return filterArray(r(...)) end end)
	spoof("filtergc",  function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	spoof("getreg",    function(r) return function(...) return filterArray(r(...)) end end)
	-- getgenv/getrenv must keep identity (callers rely on it); objects already hidden via getgc

	-- 4) INSTANCE scans -- strip our injected instances -------------------
	spoof("getinstances",    function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getnilinstances", function(r) return function(...) return filterArray(r(...)) end end)

	-- 5) SCRIPT scans -- hide our scripts/closures ------------------------
	spoof("getloadedmodules", function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getrunningscripts",function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getscripts",       function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getcallingscript", function(r) return function(...) local s = r(...); if ourScripts[s] or s == nil then return decoyScript end return s end end)
	spoof("getscriptbytecode",function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscriptclosure", function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscripthash",    function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	spoof("getsenv",          function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- 6) DEBUG introspection -- blank out for OUR functions ---------------
	if debug then
		spoofIn(debug, "getupvalue",  function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getupvalues", function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getconstant", function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getconstants",function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getproto",    function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getprotos",   function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
	end
	-- top-level mirrors (some executors expose these globally too)
	for _, n in ipairs({ "getupvalue","getupvalues","getconstant","getconstants","getproto","getprotos" }) do
		spoof(n, function(r) return function(f, ...)
			if genuineFns[f] then
				if string.sub(n, -1) == "s" then return {} end
				return nil
			end
			return r(f, ...)
		end end)
	end

	-- 7) common executor extras (Volt/Synapse/etc. spellings that may exist) ----
	for _, n in ipairs({ "getexecutorname", "getexecutor", "getexecutorinfo" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end
	-- decompiler-style probes: refuse on our scripts
	for _, n in ipairs({ "decompile", "disassemble", "dumpstring" }) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	end

	-- 7b) Potassium / extended closure + thread + hook checks --------------
	-- the big one: isfunctionhooked must say NO for the funcs your cheat hooks
	spoof("isfunctionhooked", function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isnewcclosure",    function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isourclosure",     function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	-- "is this the executor / a hook thread" -> no
	spoof("isourthread",      function(r) return function() return false end end)
	-- thread/script linkage: don't reveal our scripts
	spoof("getscriptfromthread", function(r) return function(t, ...) local s = r(t, ...) if ourScripts[s] then return nil end return s end end)
	spoof("getscriptthread",     function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("gettenv",             function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- Potassium oth.* (original-thread hooking) table
	local oth = rawget(realG, "oth")
	if type(oth) == "table" then
		spoofIn(oth, "is_hook_thread", function(r) return function() return false end end)
	end

	-- debug.* extras present on Potassium
	if debug then
		spoofIn(debug, "getcallstack", function(r) return function(...) return r(...) end end)  -- seam: frames aren't our objects
		-- getregistry: return a filtered COPY with our objects removed (AC scans are read-only)
		spoofIn(debug, "getregistry", function(r) return function(...)
			local reg = r(...)
			if type(reg) ~= "table" then return reg end
			local out = {}
			for k, v in pairs(reg) do
				if not (hiddenObjs[k] or hiddenObjs[v] or genuineFns[k] or genuineFns[v]) then
					out[k] = v
				end
			end
			return out
		end end)
		spoofIn(debug, "getinfo", function(r) return function(...) return r(...) end end)  -- seam
	end

	-- metatable seams: only safe to touch CONDITIONALLY. We do NOT blanket-fake
	-- getrawmetatable/getnamecallmethod -- faking the real game metatable breaks
	-- everything. If YOUR cheat hooks __namecall, register the clean function via
	-- Stealth.markGenuine(yourHook) and add a targeted getrawmetatable spoof.

	-- 8) USER-SUPPLIED EXTENSIONS (add Volt-specific names without editing code) -
	--    opts.identity   = { "voltname", ... }     -> spoofed like identifyexecutor
	--    opts.gcFilters  = { "somelist", ... }     -> array results have our objs removed
	--    opts.genuine    = { "iscustom", ... }     -> return clean for our funcs
	--    opts.scriptHide = { "getbytecode2", ... } -> return nothing for our scripts
	for _, n in ipairs(opts.identity or {}) do
		spoof(n, function() return function() if fakeName then return fakeName, fakeVer end return nil end end)
	end
	for _, n in ipairs(opts.gcFilters or {}) do
		spoof(n, function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	end
	for _, n in ipairs(opts.genuine or {}) do
		spoof(n, function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	end
	for _, n in ipairs(opts.scriptHide or {}) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	end

	return true
end

return Stealth

end)()
local Memory = (function()
--!nonstrict
-- ============================================================================
--  Memory.lua  --  resource scope + leak/overflow protection
--
--  Every thread, connection and disposable the VM creates is registered in a
--  scope. When the script ends (return, error, or tamper) the scope is torn down
--  deterministically: threads cancelled, connections disconnected, tables
--  cleared, GC forced. Plus a budget guard that collects GC the moment memory
--  crosses a threshold, so a runaway/hostile script can't balloon the VM.
--
--  Design notes:
--   * Registries that hold game objects use WEAK keys so they never pin memory.
--   * The scope holds STRONG refs to threads/connections (so it can cancel them)
--     but cleanup is GUARANTEED to run, bounding their lifetime.
--   * Counters are capped; nothing grows unbounded.
-- ============================================================================

local Memory = {}
Memory.__index = Memory

local taskLib   = task
local taskSpawn = (taskLib and taskLib.spawn) or spawn
local taskWait  = (taskLib and taskLib.wait) or wait
local taskDefer = (taskLib and taskLib.defer) or taskSpawn
local taskCancel = taskLib and taskLib.cancel
local cg = collectgarbage

local MAX_TRACKED = 4096   -- hard cap so the bookkeeping itself can't leak

function Memory.new()
	return setmetatable({
		alive = true,
		threads = {},
		conns = {},
		disposers = {},
		count = 0,
	}, Memory)
end

local function bounded(self)
	return self.count < MAX_TRACKED
end

-- spawn a tracked thread (auto-cancelled on cleanup)
function Memory:spawn(fn)
	if not self.alive or not bounded(self) then return end
	local co = taskSpawn(fn)
	self.threads[#self.threads + 1] = co
	self.count = self.count + 1
	return co
end

-- track an arbitrary resource with a disposer
function Memory:track(obj, dispose)
	if not self.alive or not bounded(self) then return obj end
	if dispose then
		self.disposers[#self.disposers + 1] = dispose
		self.count = self.count + 1
	end
	return obj
end

-- track a signal connection (auto-disconnected on cleanup)
function Memory:connect(signal, fn)
	if not self.alive or not bounded(self) then return end
	local ok, c = pcall(function() return signal:Connect(fn) end)
	if ok and c then
		self.conns[#self.conns + 1] = c
		self.count = self.count + 1
		return c
	end
end

-- deterministic teardown -- safe to call multiple times
function Memory:cleanup()
	if not self.alive then return end
	self.alive = false
	for _, c in ipairs(self.conns) do
		pcall(function() if c.Disconnect then c:Disconnect() elseif c.disconnect then c:disconnect() end end)
	end
	if taskCancel then
		for _, co in ipairs(self.threads) do pcall(taskCancel, co) end
	end
	for _, d in ipairs(self.disposers) do pcall(d) end
	self.conns, self.threads, self.disposers, self.count = {}, {}, {}, 0
	if cg then pcall(cg, "collect") end
end

-- memory-budget guard: force GC when usage crosses the threshold; if it stays
-- over after a collect, escalate to onOverflow (the Vm halts).
function Memory:guard(opts)
	opts = opts or {}
	local budgetKB = opts.budgetKB or 700000   -- ~700 MB ceiling by default
	local interval = opts.interval or 4
	self:spawn(function()
		while self.alive do
			taskWait(interval)
			if not self.alive then return end
			local used = cg and cg("count") or 0     -- KB
			if used > budgetKB then
				if cg then pcall(cg, "collect") end
				used = cg and cg("count") or 0
				if used > budgetKB and opts.onOverflow then
					pcall(opts.onOverflow, used)
					return
				end
			end
		end
	end)
end

return Memory

end)()
local Defense = (function()
--!nonstrict
-- ============================================================================
--  Defense.lua  --  detect tools SPYING on your script (anti-tamper)
--
--  These detect OTHER exploiters' inspection tools so your script can react
--  (halt / hide) before its logic or remotes are stolen:
--    * HTTP spy      -- request/http hooked (closure-type check vs captured original)
--    * namecall hook -- __namecall identity changed (IY-style stack inspection)
--    * remote spy    -- gcinfo spike on FireServer (spies deep-clone args)  [opt-in]
--    * Dex explorer  -- weak-table service-cache persistence                [opt-in]
--
--  IMPORTANT: this is ANTI-SPY (protect your code from other exploiters), NOT
--  anti-cheat. It does nothing against the GAME's AC -- and the remote/dex probes
--  even ADD client AC surface (they fire a remote / force GC). Keep those opt-in.
-- ============================================================================

local Defense = {}

local gcinfo_   = gcinfo or function() return (collectgarbage and collectgarbage("count")) or 0 end
local cloneref_ = cloneref or function(x) return x end
local collect   = collectgarbage
local iscc      = iscclosure       -- captured at load; Stealth passes through for non-ours
local dbinfo    = debug and debug.info

-- 1) HTTP spy: a spy hooks the global request -> it becomes an l-closure -------
-- get the real __namecall fn via an errored game:IsA() ----------------------
local function actualNamecall()
	local nc, caller
	if not dbinfo then return nil end
	xpcall(function() return game:IsA() end, function()
		nc, caller = dbinfo(2, "f"), dbinfo(3, "f")
	end)
	return nc, caller
end

local function remoteSpike()
	local ok, spike = pcall(function()
		local re = Instance.new("RemoteEvent")
		local payload = { 1, 2, 3, { nested = true }, "probe" }
		local before = gcinfo_()
		pcall(function() re:FireServer(payload) end)
		local after = gcinfo_()
		pcall(function() re:Destroy() end)
		return after - before
	end)
	return (ok and type(spike) == "number") and spike or 0
end

-- BASELINE: snapshot the environment AFTER your script has set up its own hooks,
-- so YOUR hooks are treated as "normal". Only CHANGES after this (a spy) trigger.
-- Until baseline() is called, the change-detectors stay silent (no false positives).
Defense._snap = nil
function Defense.baseline()
	local realG = (getgenv and getgenv()) or _G
	Defense._snap = {
		ready = true,
		nc = (actualNamecall()),
		request = rawget(realG, "request"),
		http_request = rawget(realG, "http_request"),
		getgc = rawget(realG, "getgc"),     -- a dumper re-hooking getgc -> identity change
		spike = remoteSpike(),
	}
	return true
end

-- getgc-scan: someone re-hooked getgc (a memory scanner/dumper) after baseline
function Defense.detectGetgcHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	local cur = rawget(realG, "getgc")
	if cur and s.getgc and cur ~= s.getgc then return true, "getgc re-hooked (memory scan)" end
	return false
end

-- spy-tool GLOBALS (Hydroxide/SimpleSpy/etc. set flags or tables in getgenv)
local SPY_GLOBALS = { "Hydroxide", "oh_load", "SimpleSpy", "SimpleSpyExecuted", "RemoteSpyV3", "IY_LOADED" }
function Defense.detectSpyGlobals()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		for _, n in ipairs(SPY_GLOBALS) do
			if rawget(g, n) ~= nil then return true, "global " .. n end
		end
	end
	return false
end

-- 1) HTTP spy: the request function IDENTITY changed since baseline (newly hooked)
function Defense.detectHttpSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	for _, n in ipairs({ "request", "http_request" }) do
		local cur = rawget(realG, n)
		if cur and s[n] and cur ~= s[n] then return true, n .. " changed after baseline" end
	end
	return false
end

-- 2) namecall hook: __namecall identity changed since baseline
function Defense.detectNamecallHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local nc = actualNamecall()
	if s.nc and nc and nc ~= s.nc then return true, "__namecall changed after baseline" end
	return false
end

-- 3) remote spy: gc spike on FireServer rose ABOVE the baseline (a new arg-cloner)
function Defense.detectRemoteSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local spike = remoteSpike()
	if spike > (s.spike or 0) + 64 then
		return true, "FireServer gc spike " .. tostring(spike)
	end
	return false
end

-- 4a) Infinite Yield (and similar admin tools) set a known global flag --------
function Defense.detectInfiniteYield()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		if rawget(g, "IY_LOADED") == true then return true, "Infinite Yield" end
	end
	return false
end

-- 4b) Spy/explorer GUIs (Dex, RemoteSpy, SimpleSpy, Hydroxide, IY window) ------
-- scans CoreGui, the executor-hidden gui (gethui), and PlayerGui by exact name.
-- PRECISE name matching: exact known names, plus controlled version patterns,
-- so we don't false-positive on legit GUIs (e.g. "Dexterity" must NOT match "dex").
local EXACT = {
	["dex"] = true, ["dex explorer"] = true, ["remotespy"] = true, ["remote spy"] = true,
	["simplespy"] = true, ["simple spy"] = true, ["hydroxide"] = true,
}
local function isSpyName(nm)
	if EXACT[nm] then return true end
	if string.match(nm, "^dex%s*v?%d") then return true end          -- "dex v4", "dex 5"
	if string.match(nm, "^remotespy") then return true end
	if string.match(nm, "^simplespy") then return true end
	if string.match(nm, "^hydroxide") then return true end
	return false
end
function Defense.detectSpyGui()
	local parents = {}
	pcall(function() parents[#parents + 1] = game:GetService("CoreGui") end)
	if gethui then pcall(function() parents[#parents + 1] = gethui() end) end
	pcall(function()
		local pg = game:GetService("Players").LocalPlayer:FindFirstChild("PlayerGui")
		if pg then parents[#parents + 1] = pg end
	end)
	for _, p in ipairs(parents) do
		local ok, kids = pcall(function() return p:GetChildren() end)
		if ok then
			for _, c in ipairs(kids) do
				if isSpyName(string.lower(c.Name)) then return true, "GUI: " .. c.Name end
			end
		end
	end
	return false
end

-- 4) Dex: it strong-caches services, so a weak ref survives a forced GC -------
function Defense.detectDex()
	local ok, persisted = pcall(function()
		local weak = setmetatable({}, { __mode = "v" })
		weak[1] = cloneref_(game:GetService("TestService"))
		weak[1] = weak[1]   -- (kept only in the weak table after this scope)
		if collect then for _ = 1, 3 do pcall(collect, "collect") end end
		return weak[1] ~= nil
	end)
	return ok and persisted == true
end

-- SaveInstance guard: hook saveinstance-family so a game/script DUMP is caught
-- the moment it's attempted. Call once (from the watchdog) with the reaction.
function Defense.installSaveGuard(onDetect)
	local realG = (getgenv and getgenv()) or _G
	local newcc_ = newcclosure or function(f) return f end
	local hookf, clonef = hookfunction, clonefunction
	for _, n in ipairs({ "saveinstance", "synsaveinstance", "SaveInstance", "saveplace" }) do
		local f = rawget(realG, n)
		if type(f) == "function" and hookf and clonef then
			local ok, orig = pcall(clonef, f)
			if ok then
				pcall(hookf, f, newcc_(function(...)
					pcall(onDetect, "saveinstance", n)
					return orig(...)
				end))
			end
		end
	end
end

-- run a scan; returns array of { name = , detail = }
function Defense.scan(opts)
	opts = opts or {}
	local found = {}
	local function run(enabled, fn, name, arg)
		if not enabled then return end
		local ok, detail = fn(arg)
		if ok then found[#found + 1] = { name = name, detail = detail or "" } end
	end
	run(opts.iy ~= false,        Defense.detectInfiniteYield, "infinite-yield")
	run(opts.gui ~= false,       Defense.detectSpyGui,        "spy-gui")     -- Dex/RemoteSpy/IY window
	run(opts.globals ~= false,   Defense.detectSpyGlobals,    "spy-global")  -- Hydroxide/SimpleSpy/etc.
	run(opts.http ~= false,      Defense.detectHttpSpy,       "http-spy")
	run(opts.namecall ~= false,  Defense.detectNamecallHook,  "namecall-hook")
	run(opts.getgc ~= false,     Defense.detectGetgcHook,     "getgc-scan")  -- dumper re-hooked getgc
	run(opts.remote == true,     Defense.detectRemoteSpy,     "remote-spy")  -- opt-in (fires a remote)
	run(opts.dex == true,        Defense.detectDex,           "dex")         -- opt-in (forces GC)
	return found
end

-- watchdog: scan promptly then on an interval; call onDetect on first hit.
-- Light probes (IY/GUI/http/namecall) run every tick; HEAVY probes (remote gc
-- spike, Dex weak-table) run only every Nth tick so they don't spam remote-fires
-- or force GC constantly. Heavy probes are ON unless explicitly set to false.
function Defense.watchdog(ctx, onDetect, opts)
	opts = opts or {}
	-- proactive SaveInstance dump guard (fires the moment a dump is attempted)
	pcall(Defense.installSaveGuard, onDetect)
	local body = function()
		local wait_ = (task and task.wait) or wait
		wait_(opts.startDelay or 1)            -- let tools finish loading
		-- reliable signals (IY global, Dex/spy GUI by name, http hook, namecall hook)
		-- react on the FIRST hit. Only the noisy probes need a 2nd confirmation.
		local NOISY = { ["remote-spy"] = true, ["dex"] = true }
		local n, lastHit, confirm = 0, nil, 0
		-- baseline after a grace period so the script's OWN hooks aren't flagged
		-- (Vm also baselines right after the main chunk; whichever fires first wins).
		local graceUntil = (tick and tick() or 0) + (opts.gracePeriod or 4)
		while ctx.alive do
			n = n + 1
			if not (Defense._snap and Defense._snap.ready) and (tick and tick() or 0) >= graceUntil then
				pcall(Defense.baseline)
			end
			local heavy = (n % (opts.heavyEvery or 5)) == 0
			local hits = Defense.scan({
				iy = opts.iy, gui = opts.gui, globals = opts.globals,
				http = opts.http, namecall = opts.namecall, getgc = opts.getgc,
				remote = (opts.remote ~= false) and heavy,   -- throttled, on by default
				dex = (opts.dex ~= false) and heavy,           -- throttled, on by default
				raw = ctx.raw,
			})
			if #hits > 0 then
				local h = hits[1]
				local need = NOISY[h.name] and 2 or 1        -- reliable = instant, noisy = confirm twice
				if h.name == lastHit then confirm = confirm + 1
				else lastHit, confirm = h.name, 1 end
				if confirm >= need then
					pcall(onDetect, h.name, h.detail)
					return
				end
			else
				lastHit, confirm = nil, 0
			end
			wait_(opts.interval or 3)
		end
	end
	if ctx.mem and ctx.mem.spawn then ctx.mem:spawn(body)
	else local s = (task and task.spawn) or spawn if s then s(body) end end
end

return Defense

end)()
local Neuter = (function()
--!nonstrict
-- ============================================================================
--  Neuter.lua  --  best-effort anti-cheat neutralizer (with honest reporting)
--
--  Attempts, in order, every CLIENT-SIDE technique to blind an AC, and REPORTS
--  the outcome of each. If it can't bypass, it says so loudly:
--      "AC bypass fail (error; <reason>)"
--  rather than silently pretending you're undetected.
--
--  Strategies:
--    1. global-spoof   -- replace detection globals with clean-answering versions
--    2. upvalue-patch  -- find ACs that captured detection fns as upvalues and
--                         debug.setupvalue them to our clean versions
--    3. table-patch    -- replace detection fns held in (writable) state tables
--                         (reaches some VM-style ACs)
--    4. report-block   -- best-effort: neutralize the global HTTP request path
--
--  HARD TRUTH (always reported): this is CLIENT-SIDE only. An AC that is
--  VM-obfuscated (functions buried in encrypted state -> nothing to patch) or
--  that validates SERVER-SIDE cannot be bypassed from here. Rivals is both.
-- ============================================================================

local Neuter = {}

local newcc   = newcclosure or function(f) return f end
local getgc_  = getgc
local getups  = getupvalues or (debug and debug.getupvalues)
local setup   = debug and debug.setupvalue
local realG   = (getgenv and getgenv()) or _G
local rawget, rawset = rawget, rawset

local SCAN_CAP = 300000

-- clean-answering replacements: AC sees "no executor, nothing hooked"
local function replacements()
	local R = {}
	R.identifyexecutor   = newcc(function() return nil end)
	R.getexecutorname    = newcc(function() return nil end)
	R.getexecutor        = newcc(function() return nil end)
	R.iscclosure         = newcc(function() return true end)   -- everything looks native
	R.isexecutorclosure  = newcc(function() return false end)
	R.isourclosure       = newcc(function() return false end)
	R.islclosure         = newcc(function() return false end)
	R.isfunctionhooked   = newcc(function() return false end)
	R.checkcaller        = newcc(function() return false end)
	R.isourthread        = newcc(function() return false end)
	return R
end

-- map ORIGINAL function identity -> replacement (for patching captured refs)
local function identityMap(R)
	local m = {}
	for name, repl in pairs(R) do
		local orig = rawget(realG, name)
		if type(orig) == "function" then m[orig] = repl end
	end
	return m
end

-- 1) global spoof -----------------------------------------------------------
function Neuter.globalSpoof(R)
	local n = 0
	for name, repl in pairs(R) do
		if type(rawget(realG, name)) == "function" then
			if hookfunction and clonefunction then
				local ok, orig = pcall(clonefunction, rawget(realG, name))
				if ok then pcall(hookfunction, rawget(realG, name), repl) else pcall(rawset, realG, name, repl) end
			else
				pcall(rawset, realG, name, repl)
			end
			n = n + 1
		end
	end
	return n > 0, "spoofed " .. n .. " globals", 0
end

-- 2) upvalue patch ----------------------------------------------------------
function Neuter.patchUpvalues(idmap)
	if not (getgc_ and getups and setup) then return false, "no getgc/debug.setupvalue" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, fn in ipairs(getgc_(false) or getgc_()) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(fn) == "function" then
				local oku, ups = pcall(getups, fn)
				if oku and type(ups) == "table" then
					for i, uv in pairs(ups) do
						if idmap[uv] then
							if pcall(setup, fn, i, idmap[uv]) then patched = patched + 1 end
						end
					end
				end
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " captured upvalue(s) of " .. scanned .. " closures", patched
end

-- 3) table patch (reaches some VM-style ACs that read fns from state tables) -
function Neuter.patchTables(idmap)
	if not getgc_ then return false, "no getgc" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, t in ipairs(getgc_(true)) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(t) == "table" then
				pcall(function()
					for k, v in pairs(t) do
						if idmap[v] then
							if pcall(function() t[k] = idmap[v] end) then patched = patched + 1 end
						end
					end
				end)
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " table slot(s)", patched
end

-- 4) report block (best-effort) --------------------------------------------
function Neuter.blockReporting()
	-- We can only neutralize a report path we can see. The global request is
	-- proxied by Secure already; an AC-internal report channel inside a VM is
	-- not generically locatable, so report this honestly.
	return false, "report channel not generically locatable (AC-internal)"
end

-- orchestrate ---------------------------------------------------------------
function Neuter.run(opts)
	opts = opts or {}
	local logf = opts.log or function(m) pcall(warn, m) end
	local R = replacements()
	local idmap = identityMap(R)

	local results, patched = {}, 0
	local function strat(name, fn, ...)
		local ok, detail, n = fn(...)
		results[#results + 1] = { name = name, ok = ok, detail = detail }
		if type(n) == "number" then patched = patched + n end
		logf("[Neuter] " .. name .. ": " .. (ok and "OK" or "FAIL") .. " -- " .. tostring(detail))
	end

	strat("global-spoof",  Neuter.globalSpoof, R)
	strat("upvalue-patch", Neuter.patchUpvalues, idmap)
	strat("table-patch",   Neuter.patchTables, idmap)
	strat("report-block",  Neuter.blockReporting)

	-- VERDICT (honest)
	local verdict
	if patched > 0 then
		verdict = "client checks neutralized (" .. patched .. " refs patched). "
			.. "WARNING: server-side validation is NOT affected -- this is not full immunity."
		logf("[Neuter] result: PARTIAL -- " .. verdict)
	else
		verdict = "no patchable detection refs found -- AC is VM-obfuscated/absent or "
			.. "captures privately; nothing to neutralize client-side."
		logf("AC bypass fail (error; " .. verdict .. ")")
	end

	return { patched = patched, results = results, ok = patched > 0, verdict = verdict }
end

return Neuter

end)()
local License = (function()
--!nonstrict
-- ============================================================================
--  License.lua  --  key / HWID whitelist, expiry, server validation, delivery
--
--  Anti-leak core. A protected script can require a valid KEY (+ optional HWID
--  lock) before it runs, enforce an EXPIRY, and/or fetch its real payload from
--  YOUR server only after the key checks out (so a leaked file is useless).
--
--  Validation order (any you configure):
--    1. expiry      -- refuse if past opts.expiry (server time when possible)
--    2. local keys  -- opts.keys = { "KEY1", ... } embedded allow-list
--    3. server      -- GET opts.endpoint?key=..&hwid=..  -> body must contain "ok"
--  If none configured, it allows (no license).
-- ============================================================================

local License = {}

local function httpGet(url)
	local fns = {
		function() return game:HttpGetAsync(url) end,
		function() return game:HttpGet(url) end,
		function() return request and request({ Url = url, Method = "GET" }).Body end,
	}
	for _, f in ipairs(fns) do
		local ok, body = pcall(f)
		if ok and type(body) == "string" then return body end
	end
	return nil
end

-- stable per-machine id
function License.hwid()
	local id
	pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
	if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
	return tostring(id or "unknown")
end

-- tamper-resistant time: try a web time source, fall back to os.time
function License.now()
	local body = httpGet("https://worldtimeapi.org/api/timezone/Etc/UTC.txt")
	if body then
		local ut = string.match(body, "unixtime:%s*(%d+)")
		if ut then return tonumber(ut) end
	end
	return os.time and os.time() or 0
end

local function inList(list, key)
	for _, k in ipairs(list) do if k == key then return true end end
	return false
end

-- returns ok, reason
function License.validate(opts)
	opts = opts or {}

	if opts.expiry then
		local now = License.now()
		if now and now > 0 and now > opts.expiry then
			return false, "license expired"
		end
	end

	if opts.endpoint then
		local hwid = License.hwid()
		local sep = string.find(opts.endpoint, "?", 1, true) and "&" or "?"
		local url = opts.endpoint .. sep .. "key=" .. tostring(opts.key or "")
			.. "&hwid=" .. hwid
		local body = httpGet(url)
		if not body then return false, "license server unreachable" end
		local lb = string.lower(body)
		if string.find(lb, "ok", 1, true) or string.find(lb, "valid", 1, true) then
			return true, "ok", body  -- body may carry the payload for server-delivery
		end
		return false, "key rejected by server"
	end

	if opts.keys then
		if opts.key and inList(opts.keys, opts.key) then return true, "ok" end
		return false, "invalid key"
	end

	return true, "no license configured"
end

-- SERVER-SIDE DELIVERY: validate, and if the server returns the (encrypted)
-- payload in its response, return it so the loader can run it. Body format the
-- reference server uses:  "ok\n<base64-xored-payload>"  (key is the xor key).
function License.deliver(opts)
	local ok, reason, body = License.validate(opts)
	if not ok then return nil, reason end
	if body then
		local nl = string.find(body, "\n", 1, true)
		if nl then return string.sub(body, nl + 1), "ok" end
	end
	return nil, "validated (no payload in response)"
end

return License

end)()
local Vm = (function()
--!nonstrict
-- ============================================================================
--  Vm.lua  --  main entry of the Vm protection runtime
--
--  Orchestrates Secure (capture+proxies), Environment (sandbox), and Integrity
--  (anti-tamper), then runs the wrapped script inside the sealed runtime.
--
--  API:
--    Vm.run(chunk [, opts])     -- chunk = source string OR a function
--    Vm.protect(fn [, opts])    -- returns a hardened wrapper of fn
--
--  opts = {
--    name     = "Sell a Lemon",      -- label for errors/telemetry
--    strict   = false,                -- abort if executor funcs look pre-hooked
--    interval = 2,                    -- watchdog period (seconds)
--    onTamper = function(reason) end, -- override default self-destruct
--    checksum = "<fnv hash>",         -- optional source integrity pin
--  }
-- ============================================================================

local Crypt       = Crypt
local Secure      = Secure
local Environment = Environment
local Integrity   = Integrity
local Stealth     = Stealth
local Memory      = Memory
local Defense     = Defense
local Neuter      = Neuter
local License     = License

local Vm = {}
Vm._VERSION = "1.0.0"

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local loadstr = loadstring or load
local setfenv_ = setfenv

-- default self-destruct: wipe the sandbox + raise, so a tampered run cannot
-- continue executing the protected logic.
local function defaultTamper(ctx, reason)
	ctx.alive = false
	-- neuter the proxies so any in-flight call resolves to nothing
	for k in pairs(ctx.proxies) do ctx.proxies[k] = nil end
	if ctx.mem then pcall(function() ctx.mem:cleanup() end) end  -- free threads/conns
	error("[Vm] integrity violation (" .. tostring(reason) .. ") -- halted", 0)
end

-- Build a fresh, sealed runtime context.
local function newContext(opts)
	-- install anti-detection FIRST (as early as we can), then hide our own
	-- objects from gc/closure scans so the spoofing can't be traced back to us.
	if opts.stealth ~= false then
		pcall(Stealth.install, opts.stealthOpts or {})
	end

	-- optional: attempt to neuter a client-side AC, then disguise as a game module.
	-- Reports "AC bypass fail (error; ...)" if it can't (VM-obfuscated / server-side).
	if opts.neuterAC then
		pcall(Neuter.run, type(opts.neuterAC) == "table" and opts.neuterAC or {})
	end

	local raw = Secure.capture()
	local proxies = Secure.proxies(raw)
	local fingerprint = Secure.fingerprint(proxies)
	local env, envMT, _store, envLock = Environment.build(proxies, realG)

	-- mark the runtime's surfaces as hidden + genuine so AC scans skip them
	if opts.stealth ~= false then
		Stealth.hide(raw); Stealth.hide(proxies); Stealth.hide(env)
		for _, fn in pairs(proxies) do
			if type(fn) == "function" then Stealth.markGenuine(fn) end
		end
	end

	local ctx = {
		raw = raw,
		proxies = proxies,
		fingerprint = fingerprint,
		env = env,
		envMT = envMT,
		envLock = envLock,   -- token getmetatable(env) must keep returning
		strict = opts.strict or false,
		interval = opts.interval or 2,
		alive = true,
		name = opts.name or "script",
		mem = Memory.new(),   -- resource scope: tracks every thread/connection
	}

	-- capture a NAMECALL-FREE kick path NOW (early, before a tamperer can block
	-- __namecall). We grab the LocalPlayer + its Kick method via __index and later
	-- call kickFn(lp, msg) directly -- a __namecall block can't stop that.
	pcall(function()
		local plrs = game:GetService("Players")
		ctx.lp = plrs.LocalPlayer
		ctx.kickFn = ctx.lp and ctx.lp.Kick
	end)

	return ctx
end

-- Core: run a function inside a sealed context with integrity enforced.
function Vm.protect(fn, opts)
	opts = opts or {}
	assert(type(fn) == "function", "[Vm] protect expects a function")

	return function(...)
		local ctx = newContext(opts)

		-- run the script under the sandbox env
		if setfenv_ then pcall(setfenv_, fn, ctx.env) end

		local onTamper = function(reason)
			if opts.onTamper then pcall(opts.onTamper, reason) end
			defaultTamper(ctx, reason)
		end

		-- startup integrity gate
		local ok, reason = Integrity.startup(ctx)
		if not ok then return onTamper(reason) end

		-- background watchdog (tracked by the memory scope)
		Integrity.watchdog(ctx, onTamper)

		-- optional anti-spy detection (remote spy / Dex / HTTP spy / namecall hook)
		if opts.antiSpy then
			local o = type(opts.antiSpy) == "table" and opts.antiSpy or {}
			Defense.watchdog(ctx, function(name, detail)
				if opts.onSpy then pcall(opts.onSpy, name, detail) end
				-- clean message (no details). Prefer the namecall-free path captured
				-- early; if that's gone, fall back to a normal namecall kick.
				if o.kick ~= false then
					local kicked = false
					if ctx.kickFn and ctx.lp then
						kicked = pcall(ctx.kickFn, ctx.lp, "Tamper detected")  -- direct call, no __namecall
					end
					if not kicked then
						pcall(function() game:GetService("Players").LocalPlayer:Kick("Tamper detected") end)
					end
				end
				-- crash the tamperer's client -- the guaranteed fallback if the kick is
				-- blocked. IMPORTANT: NOT wrapped in pcall (a pcall would swallow the
				-- out-of-memory error and stop the crash). Allocations are kept alive in
				-- `sink` so GC can't reclaim them; big chunks per iteration -> OOM in ~1s.
				-- Runs in its own thread so cleanup can't cancel it.
				if o.crash ~= false then
					local sp = (task and task.spawn) or spawn
					local wait_ = (task and task.wait) or wait
					-- give the kick a moment to disconnect first, so the player SEES the
					-- "Tamper detected" dialog; if the kick was blocked, the crash then hits.
					pcall(function() wait_(o.crashDelay or 1.5) end)
					local crasher = function()
						local sink = {}
						while true do
							if table.create then
								sink[#sink + 1] = table.create(16777216, 0)   -- ~256MB/iter
							else
								sink[#sink + 1] = string.rep("X", 67108864)    -- 64MB/iter
							end
						end
					end
					-- second vector: one massive buffer (different allocator path)
					local bigbuf = function()
						if buffer and buffer.create then local _ = buffer.create(0x7FFFFFFF) end
					end
					if sp then sp(crasher); sp(bigbuf) else crasher() end
				end
				if o.halt ~= false then
					ctx.alive = false
					pcall(function() ctx.mem:cleanup() end)
				end
			end, o)
		end

		-- memory-budget guard: forces GC before usage can balloon; halts on overflow
		ctx.mem:guard({
			budgetKB = opts.memBudgetKB,
			interval = opts.interval,
			onOverflow = function(used)
				ctx.alive = false
				if opts.onOverflow then pcall(opts.onOverflow, used) end
				pcall(function() ctx.mem:cleanup() end)
			end,
		})

		-- execute the script's main chunk
		local results = { pcall(fn, ...) }

		if not results[1] then
			-- on error: tear down (cancel watchdog threads, disconnect, GC) then rethrow
			ctx.alive = false
			pcall(function() ctx.mem:cleanup() end)
			error("[Vm:" .. ctx.name .. "] " .. tostring(results[2]), 0)
		end

		-- SUCCESS: do NOT tear down. Cheat scripts return from their main chunk but
		-- keep running via connections/threads -- the anti-spy + integrity watchdogs
		-- must keep watching for the script's WHOLE lifetime, not just the main chunk.
		-- (Teardown happens on tamper, overflow, or spy-kick.)

		-- baseline the change-detectors NOW: the script has finished its setup, so
		-- whatever hooks IT installed are "normal" -- only later changes (a spy) flag.
		if opts.antiSpy then pcall(Defense.baseline) end

		return table.unpack(results, 2)
	end
end

-- Convenience: load a source string and protect+run it.
function Vm.run(chunk, opts)
	opts = opts or {}

	-- LICENSE gate (key / HWID / expiry / server). Runs before anything executes.
	if opts.license then
		local ok, reason = License.validate(opts.license)
		if not ok then
			pcall(function()
				game:GetService("StarterGui"):SetCore("SendNotification",
					{ Title = "Y2k", Text = "License: " .. tostring(reason), Duration = 6 })
			end)
			error("[Vm] license check failed: " .. tostring(reason), 0)
		end
	end

	-- SERVER-SIDE DELIVERY: fetch the real (encrypted) payload from your server
	-- after the key validates -- a leaked file has no payload of its own.
	if opts.deliver then
		local payload, reason = License.deliver(opts.deliver)
		if not payload then error("[Vm] delivery failed: " .. tostring(reason), 0) end
		chunk = (opts.deliver.key and Crypt.open(payload, opts.deliver.key)) or payload
	end

	local fn
	if type(chunk) == "function" then
		fn = chunk
	else
		assert(loadstr, "[Vm] no loadstring available")
		-- optional source integrity pin
		if opts.checksum and Crypt.hash(chunk) ~= opts.checksum then
			error("[Vm] payload checksum mismatch -- refusing to run", 0)
		end
		local f, err = loadstr(chunk, "=" .. (opts.name or "Vm"))
		if not f then error("[Vm] load error: " .. tostring(err), 0) end
		fn = f
	end
	return Vm.protect(fn, opts)()
end

return Vm

end)()

local __k = 'UwKjquxHHAMjaEDUagqpR2fe'
local __p = 'eFoQMXuX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOdBSlFVWA8aDhpKIGUDFDMjND5yEoTlwVdrM0M+WAAdA21KF3RqZU9XUVByEkZFdVdrSlFVWGhoYW1KQWVkdUFHWQM7XAEJMFotAx0QWCo9KCEOSE9kdUFHIQI9VhMGIR4kBFwEDSkkKDkTQSQxIQ5KFhEgVgMLdR8+CFETFzpoESELAiANMUFWQ0ZqClJTbEJ9WUVFTn5oaRkCBGUDNBMDFB5ydQcIMF5BSlFVWB0Be21KQWULNxIOFRkzXDMMdV8SWDpVKys6KD0eQQclNgpVMxExWU9vdVdrSiIBASQte20nDiEhJw9HHxU9XEY8ZzxnSgIYFyc8KW0eFiAhOxJLURYnXgpFJhY9D14BEC0lJG0ZFDU0OhMTe3pyEkZFBCICKTpVKxwJExlKg8XQdREGAgQ3Eg8LIRhrCx8MWBonIyEFGWUhLQQEBAQ9QEYEOxNrGAQbVkJCYW1KQQMhNBUSAxUhEk5SdQMqCAJcQkJoYW1KQWWm1cNHNhEgVgMLdVdrSpP17GgJNDkFQTUoNA8TUV9yWgcXIxI4HlFaWCsnLSEPAjFkekEUGR8kVwpFNhsuCx8ACEJoYW1KQWWm1cNHIhg9QkZFdVdrSpP17GgJNDkFQScxLEEUFBU2QUZKdRAuCwNVV2gtJioZQWpkNg4UHBUmWwUWeVc5DwIBFysjYTkDDCA2X0FHUVByEoTl91cbDwUGWGhoYW1Kg8XQdSkGBRM6EgMCMgRnShQEDSE4bj4PDSlkJQQTAlxyUwEAdRUkBQIBC2RoJywcDjctIQRHHBc/RmxFdVdrSlGX+OpoESELGCA2dUFHUZLSpkYyNBsgOQEQHSxobm0gFCg0dU5HOB40eBMIJVdkSj8aGyQhMW1FQQMoLEFIUTE8Rg9IFDEASl5VLBg7S21KQWVkdYPn01AfWxUGdVdrSlFVmsjcYQEDFyBkBgkCEhs+VxVJdQQ/CwUGVGg7JD8cBDdkPQ4XXgI3WAkMO31rSlFVWGiqwe9KIioqMwgAAlByEoTlwVcYCwcQNSkmICoPE2U0JwQUFARyQQoKIQRBSlFVWGhoo83IQRYhIRUOHxchEkaH1eNrPzhVCDotJz5KSmUlNhUOHh5yWgkRPhIyGVFeWDwgJCAPQTUtNgoCA3pYEkZFdTI9DwMMWCQnLj1KCSQ3dQgTAlA9RQhFPBk/DwMDGSRoMiEDBSA2e0EiBxUgS0YWMBQ/Ax4bWC0wMSELCCs3dQgTAhU+VEhvt+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XCODs4X30iDFEqP2YRcwY1JgQDCikyMy8efSchEDNrHhkQFkJoYW1KFiQ2O0lFKilgeUYtIBUWSjAZCi0pJTRKDSolMQQDUZLSpkYGNBsnSj0cGjopMzRQNCsoOgADWVlyVA8XJgNlSFh/WGhoYT8PFTA2O2sCHxRYbSFLDEUANTY0PxcAFA81LQoFESQjUU1yRhQQMH1BBh4WGSRoESELGCA2JkFHUVByEkZFdVdrV1ESGSUtewoPFRYhJxcOEhV6EDYJNA4uGAJXUUIkLi4LDWUWMBELGBMzRgMBBgMkGBASHWh1YSoLDCB+EgQTIhUgRA8GMF9pOBQFFCErIDkPBRYwOhMGFhVwG2wJOhQqBlEnDSYbJD8cCCYhdUFHUVByEkZYdRAqBxRPPy08EigYFywnMElFIwU8YQMXIx4oD1NcciQnIiwGQRIrJwoUARExV0ZFdVdrSlFVWHVoJiwHBH8DMBU0FAIkWwUAfVUcBQMeCzgpIihISE8oOgIGHVAHQQMXHBk7HwUmHTo+KC4PQWV5dQYGHBVodQMRBhI5HBgWHWBqFD4PEwwqJRQTIhUgRA8GMFViYB0aGykkYQEDBi0wPA8AUVByEkZFdVdrSkxVHyklJHctBDEXMBMRGBM3GkQpPBAjHhgbH2phSyEFAiQodTcOAwQnUwowJhI5SlFVWGhoYXBKBiQpMFsgFAQBVxQTPBQuQlMjETo8NCwGNDYhJ0NOexw9UQcJdTskCRAZKCQpOCgYQWVkdUFHUU1yYgoELBI5GV85FyspLR0GADwhJ2ttGBZyXAkRdRAqBxRPMTsELiwOBCFsfEETGRU8EgEEOBJlJh4UHC0sexoLCDFsfEECHxRYOEtIdZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0UdHTGV1e0EkPj4UeyFveFpriOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6aykrNgALUTM9XAAMMld2SgoIcgsnLysDBmsDFCwiLj4TfyNFdUprSDYHFz9oIG0tADcgMA9FezM9XAAMMlkbJjA2PRcBBW1KQXhkZFNRSUhmBF9QY0R/WkdDcgsnLysDBmsHByQmJT8AEkZFdUprSCUdHWgPID8OBCtkEgAKFFJYcQkLMx4sRCI2KgEYFRI8JBdkaEFFQF5iHFZHXzQkBBccH2YdCBI4JBULdUFHUU1yEA4RIQc4UF5aCik/byoDFS0xNxQUFAIxXQgRMBk/RBIaFWcRcyY5AjctJRUlEBM5ACQENhxkJRMGESwhICM/CGopNAgJXlJYcQkLMx4sRCI0Lg0XEwIlNWVkaEFFNgI9RSciNAUvDx9XcgsnLysDBmsXFDciLjMUdTVFdUprSDYHFz8JBiwYBSAqegIIHxY7VRVHXzQkBBccH2YcDgotLQAbHiQ+UU1yEDQMMh8/KR4bDDonLW9gIioqMwgAXzERcSMrAVdrSlFVRWgLLiEFE3ZqMxMIHCIVcE5VeVd5W0FZWHp6eGRga2hpdSYGHBVyVxAAOwM4Sh0cDi1oNCMOBDdkBwQXHRkxUxIAMSQ/BQMUHy1mBiwHBAAyMA8TAnoRXQgDPBBlLycwNhwbHh0rNQ1kaEFFIxUiXg8GNAMuDiIBFzopJihEJiQpMCQRFB4mQURvX1pmSjobFz8mYT8PDCowMEELFBE0EggEOBI4SlkDHTohJyQPBWUiJw4KUQQ6V0YJPAEuShYUFS1hSw4FDyMtMk81ND0dZiM2dUprEXtVWGhoESELDzFkdUFHUVByEkZFdVdrSkxVWhgkICMePhcBd01tUVByEi4EJwEuGQVVWGhoYW1KQWVkdUFaUVIaUxQTMAQ/OBQYFzwtY2FgQWVkdTYGBRUgdQcXMRIlGVFVWGhoYW1XQWcTNBUCAyk9RxQiNAUvDx8GWmRCYW1KQQMhJxUOHRkoVxRFdVdrSlFVWGh1YW8sBDcwPA0OCxUgYQMXIx4oDy4nPWpkS21KQWUXMA0LNx89VkZFdVdrSlFVWGhofG1IMiAoOScIHhQNYCNHeX1rSlFVKy0kLR0PFWVkdUFHUVByEkZFdUprSCIQFCQYJDk1MwBmeWtHUVByYQMJOTYnBiEQDDtoYW1KQWVkdVxHUyM3XgokORsbDwUGJxoNY2FgQWVkdSMSCCM3VwJFdVdrSlFVWGhoYW1XQWcGIBg0FBU2YRIKNhxpRntVWGhoAzgTJiAlJ0FHUVByEkZFdVdrSkxVWgo9OAoPADcXIQ4EGlJ+OEZFdVcJHwglHTwNJipKQWVkdUFHUVByD0ZHFwIyOhQBPS8vY2FgQWVkdSMSCDQzWwocBhIuDiIdFzhoYW1XQWcGIBgjEBk+SzUAMBMYAh4FKzwnIiZITU9kdUFHMwUrdxAAOwMYAh4FWGhoYW1KQXhkdyMSCDUkVwgRBh8kGiIBFysjY2FgQWVkdSMSCCQgUxAAOR4lDVFVWGhoYW1XQWcGIBgzAxEkVwoMOxAGDwMWECkmNR4CDjUXIQ4EGlJ+OEZFdVcJHwgyGTosJCMpDiwqBgkIAVByD0ZHFwIyLRAHHC0mAiIDDxYsOhE0BR8xWURJX1drSlE3DTEGKCoCFQAyMA8TIhg9QkZFaFdpKAQMNiEvKTkvFyAqITIPHgABRgkGPlVnYFFVWGgKNDQvADYwMBM0BR8xWUZFdVdrV1FXOj0xBCwZFSA2BhUIEhtwHmxFdVdrKAQMOyc7LCgeCCYNIQQKUVByEltFdzU+EzIaCyUtNSQJKDEhOENLe1ByEkYnIA4IBQIYHTwhIg4YADEhdUFHTFBwcBMcFhg4BxQBESsLMyweBGdoX0FHUVAQRx8mOgQmDwUcGw4tLy4PQWVkaEFFMwUrcQkWOBI/AxIzHSYrJG9Ga2VkdUElBAkAVwQMJwMjSlFVWGhoYW1KXGVmFxQeIxUwWxQRPVVnYFFVWGgOIDsFEywwMCgTFB1yEkZFdVdrV1FXPik+Lj8DFSAbHBUCHFJ+OEZFdVcNCwcaCiE8JBkFDilkdUFHUVByD0ZHExY9BQMcDC0cLiIGMyApOhUCU1xYEkZFdScuHgImHTo+KC4PQWVkdUFHUVBvEkQ1MAM4ORQHDiErJG9Ga2VkdUEmEgQ7RAM1MAMYDwMDESstYW1KXGVmFAITGAY3YgMRBhI5HBgWHWpkS21KQWUUMBUiFhcBVxQTPBQuSlFVWGhofG1IMSAwEAYAIhUgRA8GMFVnYFFVWGgLLSwDDCQmOQQkHhQ3EkZFdVdrV1FXOyQpKCALAykhFg4DFCM3QBAMNhJpRntVWGhoAC4JBDUwBQQTNhk0RkZFdVdrSkxVWgkrIigaFRUhISYOFwRwHmxFdVdrOh0UFjwbJCgOICstOEFHUVByEltFdycnCx8BKy0tJQwECCglIQgIH1J+OEZFdVcIBR0ZHSs8ACEGICstOEFHUVByD0ZHFhgnBhQWDAkkLQwECCglIQgIH1J+OEZFdVcfGAg9GTo+JD4eIyQ3PgQTUVByD0ZHAQUyIhAHDi07NQ8LEi4hIUNLew1YOEtIdTQkDhQGWGArLiAHFCstIRhKGh49RQhJdQUuDAMQCyAtJW0YBCIxOQAVHQlyUB9FMRI9GVh/OycmJyQNTwYLESQ0UU1ySWxFdVdrSDs6IWpkYW89KQAKHDIwMCYXC0RJdVUcIjQ7MRsfABsvWWdodUMwOTUcezUyFCEOXVNZWGoOEwI5NQAAd01tUVByEkQjGjBpRlFXLwEaBAlITWVmEjMoJjEVfSkhd1trSDYnNx9qbW1IMwAXEDVFXVBwZCM3DDUOOCMsWmRCYW1KQWcGGS4oPClwHkZHGDgEJEBXVGhqcAAjLWdodUNWPDkefi8qG1VnSlMnOQEGY2FKQwsBAkNLew1YOEtIdZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0UdHTGV2e0EyJTkeYWxIeFep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N1gDSonNA1HJAQ7XhVFaFcwF3t/Hj0mIjkDDitkABUOHQN8QAMWOhs9DyEUDCBgMSweCWxOdUFHURw9UQcJdRQ+GFFIWC8pLChgQWVkdQcIA1AhVwFFPBlrGhABEHIvLCweAi1sdzo5VF4PGURMdRMkYFFVWGhoYW1KCCNkOw4TURMnQEYRPRIlSgMQDD06L20ECClkMA8De1ByEkZFdVdrCQQHWHVoIjgYWwMtOwUhGAIhRiUNPBsvQgIQH2FCYW1KQSAqMWtHUVByQAMRIAUlShIACkItLylgayMxOwITGB88EjMRPBs4RBYQDAsgID9CSE9kdUFHHR8xUwpFNh8qGFFIWAQnIiwGMSklLAQVXzM6UxQENgMuGHtVWGhoKCtKDyowdQIPEAJyRg4AO1c5DwUACiZoLyQGQSAqMWtHUVByXgkGNBtrAgMFWHVoIiULE38CPA8DNxkgQRImPR4nDllXMD0lICMFCCEWOg4TIREgRkRMX1drSlEZFyspLW0CFChkaEEEGREgCCAMOxMNAwMGDAsgKCEOLiMHOQAUAlhwehMINBkkAxVXUUJoYW1KCCNkPRMXURE8VkYNIBprHhkQFmg6JDkfEytkNgkGA1xyWhQVeVcjHxxVHSYsS21KQWU2MBUSAx5yXA8JXxIlDnt/Hj0mIjkDDitkABUOHQN8RgMJMAckGAVdCCc7aEdKQWVkOQ4EEBxybUpFPQU7SkxVLTwhLT5EBiAwFgkGA1h7OEZFdVciDFEdCjhoICMOQTUrJkETGRU8Eg4XJVkILAMUFS1ofG0pJzclOARJHxUlGhYKJl5wSgMQDD06L20eEzAhdQQJFXpyEkZFJxI/HwMbWC4pLT4PayAqMWttFwU8URIMOhlrPwUcFDtmLSIFEW0jMBUuHwQ3QBAEOVtrGAQbFiEmJmFKByttX0FHUVAmUxUOewQ7CwYbUC49Ly4eCCoqfUhtUVByEkZFdVc8AhgZHWg6NCMECCsjfUhHFR9YEkZFdVdrSlFVWGhoLSIJAClkOgpLURUgQEZYdQcoCx0ZUC4maEdKQWVkdUFHUVByEkYMM1clBQVVFyNoNSUPD2UzNBMJWVIJa1QuCFcnBR4FQmhqYWNEQTErJhUVGB41GgMXJ15iShQbHEJoYW1KQWVkdUFHUVA+XQUEOVcvHlFIWDwxMShCBiAwHA8TFAIkUwpMdUp2SlMTDSYrNSQFD2dkNA8DURc3Ri8LIRI5HBAZUGFoLj9KBiAwHA8TFAIkUwpvdVdrSlFVWGhoYW1KFSQ3Pk8QEBkmGgIRfH1rSlFVWGhoYSgEBU9kdUFHFB42G2wAOxNBYBcAFis8KCIEQRAwPA0UXxo7RhIAJ18pCwIQVGg7MT8PACFtX0FHUVAhQhQANBNrV1EGCDotIClKDjdkZU9WRHpyEkZFJxI/HwMbWCopMihKSmVsOAATGV4gUwgBOhpjQ1FfWHpobG1bSGVudRIXAxUzVkZPdRUqGRR/HSYsS0cMFCsnIQgIH1AHRg8JJlksDwUmEC0rKiEPEm1tX0FHUVA+XQUEOVcnGVFIWAQnIiwGMSklLAQVSzY7XAIjPAU4HjIdESQsaW8GBCQgMBMUBREmQURMX1drSlEcHmgkMm0eCSAqX0FHUVByEkZFORgoCx1VCyBofG0GEn8CPA8DNxkgQRImPR4nDllXKyAtIiYGBDZmfGtHUVByEkZFdR4tSgIdWDwgJCNKEyAwIBMJUQQ9QRIXPBksQgIdVh4pLTgPSGUhOwVtUVByEgMLMX1rSlFVCi08ND8EQWdpd2sCHxRYOEtIdZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0UdHTGV3e0E1ND0dZiM2X1pmSpPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8U8oOgIGHVAAVwsKIRI4SkxVA2gXIiwJCSBkaEEcDFxybQMTMBk/GVFIWCYhLW0Xa08oOgIGHVA0RwgGIR4kBFEQDi0mNT5CSE9kdUFHGBZyYAMIOgMuGV8qHT4tLzkZQSQqMUE1FB09RgMWeyguHBQbDDtmESwYBCswdRUPFB5yQAMRIAUlSiMQFSc8JD5EPiAyMA8TAlA3XAJvdVdrSiMQFSc8JD5EPiAyMA8TAlBvEjMRPBs4RAMQCyckNyg6ADEsfSIIHxY7VUggAzIFPiIqKAkcCWRgQWVkdRMCBQUgXEY3MBokHhQGVhctNygEFTZOMA8De3o0RwgGIR4kBFEnHSUnNSgZTyIhIUkMFAl7OEZFdVciDFEnHSUnNSgZTxonNAIPFCs5Vx84dRYlDlEnHSUnNSgZTxonNAIPFCs5Vx84eycqGBQbDGg8KSgEQTchIRQVH1AAVwsKIRI4RC4WGSsgJBYBBDwZdQQJFXpyEkZFORgoCx1VFiklJG1XQQYrOwcOFl4AdysqATIYMRoQARVoLj9KCiA9X0FHUVA+XQUEOVcuHFFIWC0+JCMeEm1tbkEOF1A8XRJFMAFrHhkQFmg6JDkfEytkOwgLURU8VmxFdVdrBh4WGSRoM21XQSAybycOHxQUWxQWITQjAx0RUCYpLChDa2VkdUEOF1AgEhINMBlrOBQYFzwtMmM1AiQnPQQ8GhUrb0ZYdQVrDx8RcmhoYW0YBDExJw9HA3o3XAJvXxE+BBIBEScmYR8PDCowMBJJFxkgV04OMA5nSl9bVmFCYW1KQSkrNgALUQJyD0Y3MBokHhQGVi8tNWUBBDxtbkEOF1A8XRJFJ1c/AhQbWDotNTgYD2UiNA0UFFA3XAJvdVdrSh0aGykkYSwYBjZkaEETEBI+V0gVNBQgQl9bVmFCYW1KQSkrNgALUR85EltFJRQqBh1dHj0mIjkDDitsfEEVSzY7QAM2MAU9DwNdDCkqLShEFCs0NAIMWREgVRVJdUZnShAHHztmL2RDQSAqMUhtUVByEhQAIQI5BFEaE0ItLylgayMxOwITGB88EjQAOBg/DwJbESY+LiYPSS4hLE1HX158G2xFdVdrBh4WGSRoM21XQRchOA4TFAN8VQMRfRwuE1hOWCEuYSMFFWU2dRUPFB5yQAMRIAUlShcUFDstYSgEBU9kdUFHHR8xUwpFNAUsGVFIWDwpIyEPTzUlNgpPX158G2xFdVdrBh4WGSRoMygZFCkwJkFaUQtyQgUEORtjDAQbGzwhLiNCSGU2MBUSAx5yQFwsOwEkARQmHTo+JD9CFSQmOQRJBB4iUwUOfRY5DQJZWHlkYSwYBjZqO0hOURU8Vk9FKH1rSlFVES5oLyIeQTchJhQLBQMJAztFIR8uBFEHHTw9MyNKByQoJgRHFB42OEZFdVc/CxMZHWY6JCAFFyBsJwQUBBwmQUpFZF5BSlFVWDotNTgYD2UwJxQCXVAmUwQJMFk+BAEUGyNgMygZFCkwJkhtFB42OGxIeFep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N1gTGhkYU9HNzEAf0Y3ECQEJiQhMQcGYWUMCCsgdRELEAk3QEEWdRg8BBQRWC4pMyBKCCtkIg4VGgMiUwUAfH1mR1GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NVOOQ4EEBxydAcXOFd2SgoIciQnIiwGQRoiNBMKXVANXgcWISUuGR4ZDi1ofG0ECClodVFtexYnXAURPBglSjcUCiVmMygZDikyMElOe1ByEkYMM1cUDBAHFWgpLylKPiMlJwxJIREgVwgRdRYlDlEBESsjaWRKTGUbOQAUBSI3QQkJIxJrVlFAWDwgJCNKEyAwIBMJUS80UxQIdRIlDntVWGhoLSIJAClkMwAVHANyD0YyOgUgGQEUGy1yByQEBQMtJxITMhg7XgJNdzEqGBxXUUJoYW1KCCNkOw4TURYzQAsWdQMjDx9VCi08ND8EQSstOUECHxRYEkZFdREkGFEqVGguYSQEQSw0NAgVAlg0UxQIJk0MDwU2ECEkJT8PD21tfEEDHnpyEkZFdVdrSh0aGykkYSQHEWV5dQddNxk8ViAMJwQ/KRkcFCxgYwQHESo2IQAJBVJ7OEZFdVdrSlFVFCcrICFKBSQwNEFaURk/QkYEOxNrAxwFQg4hLyksCDc3ISIPGBw2GkQhNAMqSFh/WGhoYW1KQWUoOgIGHVA9RQgAJ1d2ShUUDCloICMOQSElIQBdNxk8ViAMJwQ/KRkcFCxgYwIdDyA2d0htUVByEkZFdVciDFEaDyYtM20LDyFkOhYJFAJ8ZAcJIBJrV0xVNCcrICE6DSQ9MBNJPxE/V0YRPRIlYFFVWGhoYW1KQWVkdT4BEAI/EltFM0xrNR0UCzwaJD4FDTMhdVxHBRkxWU5MX1drSlFVWGhoYW1KQTchIRQVH1ANVAcXOH1rSlFVWGhoYSgEBU9kdUFHFB42OAMLMX1BR1xVOSQkYT0GACswdQwIFRU+QUYKO1c/AhRVHik6LEcMFCsnIQgIH1AUUxQIexAuHiEZGSY8MmVDa2VkdUELHhMzXkYDdUprLBAHFWY6JD4FDTMhfUhcURk0EggKIVctSgUdHSZoMygeFDcqdRoaURU8VmxFdVdrBh4WGSRoKCAaQXhkM1shGB42dA8XJgMIAhgZHGBqCCAaDjcwNA8TU1lpEg8DdRkkHlEcFThoNSUPD2U2MBUSAx5ySRtFMBkvYFFVWGgkLi4LDWU0OQAJBQNyD0YMOAdxLBgbHA4hMz4eIi0tOQVPUyA+UwgRJigbAggGESspLW9Da2VkdUEOF1A8XRJFJRsqBAUGWDwgJCNKESklOxUUUU1yWwsVbzEiBBUzETo7NQ4CCCkgfUM3HRE8RhVHfFcuBBV/WGhoYSQMQSsrIUEXHRE8RhVFIR8uBFEHHTw9MyNKGjhkMA8De1ByEkYXMAM+GB9VCCQpLzkZWwIhISIPGBw2QAMLfV5BDx8RckJlbG0rDSlkJwgXFFB9Eg4EJwEuGQUUGiQtYT0GACswJmsBBB4xRg8KO1cNCwMYVi8tNR8DESAUOQAJBQN6G2xFdVdrBh4WGSRoLjgeQXhkLhxtUVByEgAKJ1cURlEFWCEmYSQaACw2JkkhEAI/HAEAIScnCx8BC2BhaG0ODk9kdUFHUVByEg8DdQdxIwI0UGoFLikPDWdtdRUPFB5YEkZFdVdrSlFVWGhobGBKLSorPkEBHgJyVBQQPAM4Sl5VCDonLD0eEmUtOxIOFRVyQgoEOwNrBx4RHSRCYW1KQWVkdUFHUVByXgkGNBtrDAMAETw7YXBKEX8CPA8DNxkgQRImPR4nDllXPjo9KDkZQ2xOdUFHUVByEkZFdVdrAxdVHjo9KDkZQTEsMA9tUVByEkZFdVdrSlFVWGhoYSsFE2UbeUEBA1A7XEYMJRYiGAJdHjo9KDkZWwIhISIPGBw2QAMLfV5iShUaWDwpIyEPTywqJgQVBVg9RxJJdRE5Q1EQFixCYW1KQWVkdUFHUVByVwoWMH1rSlFVWGhoYW1KQWVkdUFHXF1yYgoEOwM4SgYcDCAnNDlKBzcxPBVHFx8+VgMXJlcmCwhVCyEvLywGQTctJQQJFAMhEhAMNFcqHgUHESo9NShgQWVkdUFHUVByEkZFdVdrShgTWDhyBigeIDEwJwgFBAQ3GkQ3PAcuSFhVRXVoNT8fBGUwPQQJUQQzUAoAex4lGRQHDGAnNDlGQTVtdQQJFXpyEkZFdVdrSlFVWGgtLylgQWVkdUFHUVA3XAJvdVdrShQbHEJoYW1KEyAwIBMJUR8nRmwAOxNBYBcAFis8KCIEQQMlJwxJFhUmYRYEIhkbBQJdUUJoYW1KDSonNA1HF1BvEiAEJxplGBQGFyQ+JGVDWmUtM0EJHgRyVEYRPRIlSgMQDD06L20ECClkMA8De1ByEkYJOhQqBlEGCGh1YStQJywqMScOAwMmcQ4MORNjSCIFGT8mHh0FCCswd0hHHgJyVFwjPBkvLBgHCzwLKSQGBW1mFgQJBRUgbTYKPBk/SFh/WGhoYSQMQTY0dQAJFVAhQlwsJjZjSDMUCy0YID8eQ2xkIQkCH1AgVxIQJxlrGQFbKCc7KDkDDitkMA8DexU8VmxvMwIlCQUcFyZoBywYDGsjMBUkFB4mVxRNfH1rSlFVFCcrICFKB2V5dScGAx18QAMWOhs9D1lcQ2ghJ20EDjFkM0ETGRU8EhQAIQI5BFEbESRoJCMOa2VkdUELHhMzXkYWJVd2ShdPPiEmJQsDEzYwFgkOHRR6ECUAOwMuGC4lFyEmNW9Da2VkdUEOF1AhQkYEOxNrGQFPMTsJaW8oADYhBQAVBVJ7EhINMBlrGBQBDTomYT4aTxUrJggTGB88EgMLMX1rSlFVCi08ND8EQQMlJwxJFhUmYRYEIhkbBQJdUUItLylga2hpdYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxX1mR1FAVmgbFQw+Mk9peEGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOdBBh4WGSRoEjkLFTZkaEEcUQA+UwgRMBNrV1FFVGggID8cBDYwMAVHTFBiHkYWOhsvSkxVSGRoIyIfBi0wdVxHQVxyQQMWJh4kBCIBGTo8YXBKFSwnPklOUQ1YVBMLNgMiBR9VKzwpNT5EEyA3MBVPWFABRgcRJlk7BhAbDC0sbW05FSQwJk8PEAIkVxURMBNnSiIBGTw7bz4FDSFodTITEAQhHAQKIBAjHlFIWHhkcWFaTXV/dTITEAQhHBUAJgQiBR8mDCk6NW1XQTEtNgpPWFA3XAJvMwIlCQUcFyZoEjkLFTZqIBETGB03Gk9vdVdrSh0aGykkYT5KXGUpNBUPXxY+XQkXfQMiCRpdUWhlYR4eADE3exICAgM7XQg2IRY5Hlh/WGhoYSEFAiQodQlHTFA/UxINexEnBR4HUDtobm1ZV3V0fFpHAlBvEhVFeFcjSltVS354cUdKQWVkOQ4EEBxyX0ZYdRoqHhlbHiQnLj9CEmVrdVdXWEtyEkYWdUprGVFYWCVoa21cUU9kdUFHAxUmRxQLdQQ/GBgbH2YuLj8HADFsd0RXQxRoF1ZXMU1uWkMRWmRoKWFKDGlkJkhtFB42OGxIeFep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N1gTGhkY09HMCUGfUYiFCUPLz9/VWVoo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3exw9UQcJdTY+Hh4yGTosJCNKXGU/dTITEAQ3EltFLn1rSlFVGT08Lh0GACswdUFHUU1yVAcJJhJnSgEZGSY8EigPBWVkdUFHTFA8WwpJdVc7BhAbDAwtLSwTQWVkaEFXX0V+OEZFdVcqHwUaMCk6NygZFWVkaEEBEBwhV0pFPRY5HBQGDAEmNSgYFyQodVxHQl5iHmxFdVdrCwQBFwsnLSEPAjFkdVxHFxE+QQNJdRQkBh0QGzwBLzkPEzMlOUFaUUR8AkpvdVdrShAADCcbJCEGQWVkdUFaURYzXhUAeVc4Dx0ZMSY8JD8cAClkdVxHQkB+OEZFdVcqHwUaLyk8JD9KQWVkaEEBEBwhV0pFIhY/DwM8FjwtMzsLDWV5dVdXXXpyEkZFNAI/BSIdFz4tLW1KQXhkMwALAhV+EhUNOgEuBjgbDC06NywGQXhkZFFLUQM6XRAAOTwuDwFVRWgzPGFgQWVkdQsOBQQ3QEZFdVdrSlFIWDw6NChGazg5X2sLHhMzXkYDIBkoHhgaFmgiKDlCF2xkJwQTBAI8EicQIRgMCwMRHSZmEjkLFSBqPwgTBRUgEgcLMVceHhgZC2YiKDkeBDdsI01HQV5jAE9FOgVrHFEQFixCS2BHQQMtOwVHEFA6VwoBdQQuDxVVDCcnLW0IGGUqNAwCexw9UQcJdRE+BBIBEScmYSsDDyEXMAQDJR89Xk4LNBouQ3tVWGhoLSIJAClkNgkGA1BvEioKNhYnOh0UAS06bw4CADclNhUCA3pyEkZFORgoCx1VGikrKj0LAi5kaEErHhMzXjYJNA4uGEszESYsByQYEjEHPQgLFVhwcAcGPgcqCRpXUUJoYW1KDSonNA1HFwU8URIMOhlrGhgWE2A4ID8PDzFtX0FHUVByEkZFMxg5Si5ZWDxoKCNKCDUlPBMUWQAzQAMLIU0MDwU2ECEkJT8PD21tfEEDHnpyEkZFdVdrSlFVWGghJ20eWww3FElFJR89XkRMdQMjDx9/WGhoYW1KQWVkdUFHUVByEgoKNhYnShdVRWg8ewoPFQQwIRMOEwUmV05HM1ViYFFVWGhoYW1KQWVkdUFHUVA7VEYDdUp2Sh8UFS1oNSUPD2U2MBUSAx5yRkYAOxNBSlFVWGhoYW1KQWVkdUFHURk0EhJLGxYmD0sTESYsaW80Q2Vqe0EJEB03G0YRPRIlSgMQDD06L20eQSAqMWtHUVByEkZFdVdrSlFVWGhoKCtKFWsKNAwCSxY7XAJNd1IQORQQHG0VY2RKACsgdUkTXz4zXwNfORg8DwNdUXIuKCMOSSslOARdHR8lVxRNfFtrW11VDDo9JGRDQTEsMA9HAxUmRxQLdQNrDx8RcmhoYW1KQWVkdUFHURU8VmxFdVdrSlFVWC0mJUdKQWVkMA8De1ByEkYXMAM+GB9VUCsgID9KACsgdREOEht6UQ4EJ15iSh4HWGAqIC4BESQnPkEGHxRyQg8GPl8pCxIeCCkrKmRDayAqMWttFwU8URIMOhlrKwQBFw8pMykPD2shJBQOASM3VwJNOxYmD1h/WGhoYSQMQSsrIUEJEB03EhINMBlrGBQBDTomYSsLDTYhdQQJFXpyEkZFORgoCx1VDCcnLW1XQSMtOwU0FBU2ZgkKOV8lCxwQUUJoYW1KCCNkOw4TUQQ9XQpFIR8uBFEHHTw9MyNKByQoJgRHFB42OEZFdVcnBRIUFGgrKSwYQXhkGQ4EEBwCXgccMAVlKRkUCikrNSgYa2VkdUEOF1AmXQkJeycqGBQbDGg2fG0JCSQ2dRUPFB5YEkZFdVdrSlEBFyckbx0LEyAqIUFaURM6UxRvdVdrSlFVWGg8ID4BTzIlPBVPQV5jG2xFdVdrDx8RcmhoYW0YBDExJw9HBQInV2wAOxNBYBcAFis8KCIEQQQxIQ4gEAI2VwhLJgMqGAU0DTwnESELDzFsfGtHUVByWwBFFAI/BTYUCiwtL2M5FSQwME8GBAQ9YgoEOwNrHhkQFmg6JDkfEytkMA8De1ByEkYkIAMkLRAHHC0mbx4eADEhewASBR8CXgcLIVd2SgUHDS1CYW1KQRAwPA0UXxw9XRZNMwIlCQUcFyZgaG0YBDExJw9HGxkmGicQIRgMCwMRHSZmEjkLFSBqJQ0GHwQWVwoELF5rDx8RVEJoYW1KQWVkdQcSHxMmWwkLfV5rGBQBDTomYQwfFSoDNBMDFB58YRIEIRJlCwQBFxgkICMeQSAqMU1HFwU8URIMOhljQ3tVWGhoYW1KQWVkdUELHhMzXkYWMBIvSkxVOT08LgoLEyEhO080BREmV0gVORYlHiIQHSxCYW1KQWVkdUFHUVByWwBFOxg/SgIQHSxoLj9KEiAhMUFaTFBwEEYRPRIlSgMQDD06L20PDyFOdUFHUVByEkZFdVdrAxdVFic8YQwfFSoDNBMDFB58VxcQPAcYDxQRUDstJClDQTEsMA9HAxUmRxQLdRIlDntVWGhoYW1KQWVkdUFKXFABVwgBdRZrGh0UFjxoMygbFCA3IUEGBVAzEhYKJh4/Ax4bWCEmMiQOBGUrIBNHFxEgX2xFdVdrSlFVWGhoYW0GDiYlOUEEFB4mVxRFaFcNCwMYVi8tNQ4PDzEhJ0lOe1ByEkZFdVdrSlFVWCEuYSMFFWUnMA8TFAJyRg4AO1c5DwUACiZoJCMOa2VkdUFHUVByEkZFdVpmSiIFCi0pJW0aDSQqIRJHAxE8VgkIOQ5rCwMaDSYsYTkCBGUnMA8TFAJYEkZFdVdrSlFVWGhoLSIJAClkPwgTBRUgakZYdV8mCwUdVjopLykFDG1tdUxHQV5nG0ZPdUR7YFFVWGhoYW1KQWVkdQ0IEhE+EgwMIQMuGCtVRWhgLCweCWs2NA8DHh16G0ZIdUdlX1hVUmh7cUdKQWVkdUFHUVByEkYJOhQqBlEFFztofG0JBCswMBNHWlAEVwUROgV4RB8QD2AiKDkeBDcceUFXXVA4WxIRMAURQ3tVWGhoYW1KQWVkdUE1FB09RgMWexEiGBRdWhgkICMeQ2lkJQ4UXVAhVwMBfH1rSlFVWGhoYW1KQWUXIQATAl4iXgcLIRIvSkxVKzwpNT5EESklOxUCFVB5EldvdVdrSlFVWGgtLylDayAqMWsBBB4xRg8KO1cKHwUaPyk6JSgETzYwOhEmBAQ9YgoEOwNjQ1E0DTwnBiwYBSAqezITEAQ3HAcQIRgbBhAbDGh1YSsLDTYhdQQJFXpYVBMLNgMiBR9VOT08LgoLEyEhO08UBREgRicQIRgDCwMDHTs8aWRgQWVkdQgBUTEnRgkiNAUvDx9bKzwpNShEADAwOikGAwY3QRJFIR8uBFEHHTw9MyNKBCsgX0FHUVATRxIKEhY5DhQbVhs8IDkPTyQxIQ4vEAIkVxURdUprHgMAHUJoYW1KNDEtORJJHR89Qk4DIBkoHhgaFmBhYT8PFTA2O0EmBAQ9dQcXMRIlRCIBGTwtbyULEzMhJhUuHwQ3QBAEOVcuBBVZcmhoYW1KQWVkMxQJEgQ7XQhNfFc5DwUACiZoADgeDgIlJwUCH14BRgcRMFkqHwUaMCk6NygZFWUhOwVLURYnXAURPBglQlh/WGhoYW1KQWVkdUFHFx8gEjlJdQcnCx8BWCEmYSQaACw2JkkhEAI/HAEAIScnCx8BC2BhaG0ODk9kdUFHUVByEkZFdVdrSlFVES5oLyIeQQQxIQ4gEAI2VwhLBgMqHhRbGT08LgULEzMhJhVHBRg3XEYXMAM+GB9VHSYsS21KQWVkdUFHUVByEkZFdVcnBRIUFGgnKm1XQRchOA4TFAN8WwgTOhwuQlM9GTo+JD4eQ2lkJQ0GHwR7OEZFdVdrSlFVWGhoYW1KQWUtM0EIGlAmWgMLdSQ/CwUGViApMzsPEjEhMUFaUSMmUxIWex8qGAcQCzwtJW1BQXRkMA8De1ByEkZFdVdrSlFVWGhoYW0eADYvexYGGAR6AkhVYF5BSlFVWGhoYW1KQWVkMA8De1ByEkZFdVdrDx8RUUItLylgBzAqNhUOHh5ycxMROjAqGBUQFmY7NSIaIDAwOikGAwY3QRJNfFcKHwUaPyk6JSgETxYwNBUCXxEnRgktNAU9DwIBWHVoJywGEiBkMA8De3o0RwgGIR4kBFE0DTwnBiwYBSAqexITEAImcxMROjQkBh0QGzxgaEdKQWVkPAdHMAUmXSEEJxMuBF8mDCk8JGMLFDErFg4LHRUxRkYRPRIlSgMQDD06L20PDyFOdUFHUTEnRgkiNAUvDx9bKzwpNShEADAwOiIIHRw3URJFaFc/GAQQcmhoYW0/FSwoJk8LHh8iGgAQOxQ/Ax4bUGFoMygeFDcqdSASBR8VUxQBMBllOQUUDC1mIiIGDSAnISgJBRUgRAcJdRIlDl1/WGhoYW1KQWUiIA8EBRk9XE5MdQUuHgQHFmgJNDkFJiQ2MQQJXyMmUxIAexY+Hh42FyQkJC4eQSAqMU1HFwU8URIMOhljQ3tVWGhoYW1KQWVkdUFKXFAFUwoOdRg9DwNVCiE4JG0MEzAtIRJHAh9yRg4ALFcqHwUaVSsnLSEPAjFOdUFHUVByEkZFdVdrBh4WGSRoHmFKCTc0dVxHJAQ7XhVLMhI/KRkUCmBhS21KQWVkdUFHUVByEg8DdRkkHlEdCjhoNSUPD2U2MBUSAx5yVwgBX1drSlFVWGhoYW1KQSkrNgALUR8gWwEMOxYnSkxVEDo4bw4sEyQpMGtHUVByEkZFdVdrSlETFzpoHmFKBzdkPA9HGAAzWxQWfTEqGBxbHy08EyQaBBUoNA8TAlh7G0YBOn1rSlFVWGhoYW1KQWVkdUFHGBZyXAkRdTY+Hh4yGTosJCNEMjElIQRJEAUmXSUKORsuCQVVDCAtL20IEyAlPkECHxRYEkZFdVdrSlFVWGhoYW1KQSwidQcVSzkhc05HFxY4DyEUCjxqaG0eCSAqX0FHUVByEkZFdVdrSlFVWGhoYW1KCTc0eyIhAxE/V0ZYdTQNGBAYHWYmJDpCBzdqBQ4UGAQ7XQhFflcdDxIBFzp7byMPFm10eUFUXVBiG09vdVdrSlFVWGhoYW1KQWVkdUFHUVAmUxUOewAqAwVdSGZ4eWRgQWVkdUFHUVByEkZFdVdrShQZCy0hJ20ME38NJiBPUz09VgMJd15rCx8RWC46bx0YCCglJxg3EAImEhINMBlBSlFVWGhoYW1KQWVkdUFHUVByEkYNJwdlKTcHGSUtYXBKIgM2NAwCXx43RU4DJ1kbGBgYGToxESwYFWsUOhIOBRk9XEZOdSEuCQUaCntmLygdSXVodVJLUUB7G2xFdVdrSlFVWGhoYW1KQWVkdUFHUQQzQQ1LIhYiHllFVnhwaEdKQWVkdUFHUVByEkZFdVdrDx8RcmhoYW1KQWVkdUFHURU8VmxFdVdrSlFVWGhoYW0CEzVqFicVEB03EltFOgUiDRgbGSRCYW1KQWVkdUECHxR7OAMLMX0tHx8WDCEnL20rFDErEgAVFRU8HBUROgcKHwUaOyckLSgJFW1tdSASBR8VUxQBMBllOQUUDC1mIDgeDgYrOQ0CEgRyD0YDNBs4D1EQFixCSysfDyYwPA4JUTEnRgkiNAUvDx9bCzwpMzkrFDErBgQLHVh7OEZFdVciDFE0DTwnBiwYBSAqezITEAQ3HAcQIRgYDx0ZWDwgJCNKEyAwIBMJURU8VmxFdVdrKwQBFw8pMykPD2sXIQATFF4zRxIKBhInBlFIWDw6NChgQWVkdTQTGBwhHAoKOgdjDAQbGzwhLiNCSGU2MBUSAx5ycxMROjAqGBUQFmYbNSweBGs3MA0LOB4mVxQTNBtrDx8RVEJoYW1KQWVkdQcSHxMmWwkLfV5rGBQBDTomYQwfFSoDNBMDFB58YRIEIRJlCwQBFxstLSFKBCsgeUEBBB4xRg8KO19iYFFVWGhoYW1KQWVkdTMCHB8mVxVLMx45D1lXKy0kLQsFDiFmfGtHUVByEkZFdVdrSlEmDCk8MmMZDikgdVxHIgQzRhVLJhgnDlFeWHlCYW1KQWVkdUECHxR7OAMLMX0tHx8WDCEnL20rFDErEgAVFRU8HBUROgcKHwUaKy0kLWVDQQQxIQ4gEAI2VwhLBgMqHhRbGT08Lh4PDSlkaEEBEBwhV0YAOxNBYBcAFis8KCIEQQQxIQ4gEAI2VwhLJgMqGAU0DTwnFiweBDdsfGtHUVByWwBFFAI/BTYUCiwtL2M5FSQwME8GBAQ9ZQcRMAVrHhkQFmg6JDkfEytkMA8De1ByEkYkIAMkLRAHHC0mbx4eADEhewASBR8FUxIAJ1d2SgUHDS1CYW1KQRAwPA0UXxw9XRZNMwIlCQUcFyZgaG0YBDExJw9HMAUmXSEEJxMuBF8mDCk8JGMdADEhJygJBRUgRAcJdRIlDl1/WGhoYW1KQWUiIA8EBRk9XE5MdQUuHgQHFmgJNDkFJiQ2MQQJXyMmUxIAexY+Hh4iGTwtM20PDyFodQcSHxMmWwkLfV5BSlFVWGhoYW1KQWVkBwQKHgQ3QUgMOwEkARRdWh8pNSgYJiQ2MQQJAlJ7OEZFdVdrSlFVHSYsaEcPDyFOMxQJEgQ7XQhFFAI/BTYUCiwtL2MZFSo0FBQTHiczRgMXfV5rKwQBFw8pMykPD2sXIQATFF4zRxIKAhY/DwNVRWguICEZBGUhOwVte11/EoTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6EJlbG1dT2UFADUoUSMafTZFt/ffShMAATtoNiULFSAyMBNAAlAzRAcMORYpBhRVFyZoIG0JDisiPAYSAxEwXgNFPBk/DwMDGSRCbGBKg9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XCOAoKNhYnSjAADCcbKSIaQXhkLkE0BREmV0ZYdQxBSlFVWDstJCkkACghJkFHUU1ySRtJdRY+Hh4mHS0sMm1XQSMlORICXXpyEkZFMhIqGD8UFS07YW1KXGU/KE1HEAUmXSEANAVrSkxVHikkMihGa2VkdUECFhccUwsAJldrSlFIWDM1bW0LFDErEAYAAlByD0YDNBs4D11/WGhoYS4FEighIQgEAlByEltFMxYnGRRZcmhoYW0DDzEhJxcGHVByEkZYdUJlWl1/WGhoYSgcBCswBgkIAVByEltFMxYnGRRZcmhoYW0ECCIsIUFHUVByEkZYdREqBgIQVEJoYW1KFTclIwQLGB41EkZFaFctCx0GHWRCPDBgayMxOwITGB88EicQIRgYAh4FVjs8ID8eSWxOdUFHURk0EicQIRgYAh4FVhc6NCMECCsjdRUPFB5yQAMRIAUlShQbHEJoYW1KIDAwOjIPHgB8bRQQOxkiBBZVRWg8MzgPa2VkdUEyBRk+QUgJOhg7QhcAFis8KCIESWxkJwQTBAI8EicQIRgYAh4FVhs8IDkPTywqIQQVBxE+EgMLMVtBSlFVWGhoYW0MFCsnIQgIH1h7EhQAIQI5BFE0DTwnEiUFEWsbJxQJHxk8VUYAOxNnShcAFis8KCIESWxOdUFHUVByEkZFdVdrBh4WGSRoMm1XQQQxIQ40GR8iHDURNAMuYFFVWGhoYW1KQWVkdQgBUQN8UxMROiQuDxUGWDwgJCNgQWVkdUFHUVByEkZFdVdrShcaCmgXbW0EQSwqdQgXEBkgQU4WewQuDxU7GSUtMmRKBSpOdUFHUVByEkZFdVdrSlFVWGhoYW04BCgrIQQUXxY7QANNdzU+EyIQHSxqbW0ESE9kdUFHUVByEkZFdVdrSlFVWGhoYR4eADE3ewMIBBc6RkZYdSQ/CwUGVionNCoCFWVvdVBtUVByEkZFdVdrSlFVWGhoYW1KQWUwNBIMXwczWxJNZVl6Q3tVWGhoYW1KQWVkdUFHUVByVwgBX1drSlFVWGhoYW1KQSAqMWtHUVByEkZFdVdrSlEcHmg7bywfFSoDMAAVUQQ6VwhvdVdrSlFVWGhoYW1KQWVkdQcIA1ANHkYLdR4lShgFGSE6MmUZTyIhNBMpEB03QU9FMRhBSlFVWGhoYW1KQWVkdUFHUVByEkY3MBokHhQGVi4hMyhCQwcxLCYCEAJwHkYLfH1rSlFVWGhoYW1KQWVkdUFHUVByEjURNAM4RBMaDS8gNW1XQRYwNBUUXxI9RwENIVdgSkB/WGhoYW1KQWVkdUFHUVByEkZFdVc/CwIeVj8pKDlCUWt1fGtHUVByEkZFdVdrSlFVWGhoJCMOa2VkdUFHUVByEkZFdRIlDntVWGhoYW1KQWVkdUEOF1AhHAcQIRgODRYGWDwgJCNgQWVkdUFHUVByEkZFdVdrShcaCmgXbW0EQSwqdQgXEBkgQU4WexIsDT8UFS07aG0ODk9kdUFHUVByEkZFdVdrSlFVWGhoYR8PDCowMBJJFxkgV05HFwIyOhQBPS8vY2FKD2xOdUFHUVByEkZFdVdrSlFVWGhoYW05FSQwJk8FHgU1WhJFaFcYHhABC2YqLjgNCTFkfkFWe1ByEkZFdVdrSlFVWGhoYW1KQWVkIQAUGl4lUw8RfUdlW1h/WGhoYW1KQWVkdUFHUVByEgMLMX1rSlFVWGhoYW1KQWUhOwVtUVByEkZFdVdrSlFVES5oMmMPFyAqITIPHgByEkYRPRIlSiMQFSc8JD5EByw2MElFMwUrdxAAOwMYAh4FWmFzYR8PDCowMBJJFxkgV05HFwIyLxAGDC06EjkFAi5mfEECHxRYEkZFdVdrSlFVWGhoKCtKEmsqPAYPBVByEkZFdVc/AhQbWBotLCIeBDZqMwgVFFhwcBMcGx4sAgUwDi0mNR4CDjVmfEECHxRYEkZFdVdrSlFVWGhoKCtKEmswJwARFBw7XAFFdVc/AhQbWBotLCIeBDZqMwgVFFhwcBMcAQUqHBQZESYvY2RKBCsgX0FHUVByEkZFMBkvQ3sQFixCJzgEAjEtOg9HMAUmXTUNOgdlGQUaCGBhYQwfFSoXPQ4XXy8gRwgLPBksSkxVHikkMihKBCsgX2tKXFCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+F/VWVoeWNKIBAQGkE3NCQBOEtIdZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0UcGDiYlOUEmBAQ9YgMRJld2SgpVKzwpNShKXGU/X0FHUVAzRxIKBhInBiEQDDtofG0MACk3ME1HAhU+XjYAIT4lHhQHDikkYXBKUnVoX0FHUVAhVwoJBRI/JxgbOS8tYXBKUGlkeExHAhU+XkYVMAM4SggaDSYvJD9KFS0lO0ETGRkhOBsYX30tHx8WDCEnL20rFDErBQQTAl4hVwoJFBsnQlh/WGhoYR8PDCowMBJJFxkgV05HBhInBjAZFBgtNT5ISE8hOwVtexYnXAURPBglSjAADCcYJDkZTzYwNBMTWVlYEkZFdR4tSjAADCcYJDkZTxo2IA8JGB41EhINMBlrGBQBDTomYSgEBU9kdUFHMAUmXTYAIQRlNQMAFiYhLypKXGUwJxQCe1ByEkYwIR4nGV8ZFyc4aSsfDyYwPA4JWVlyQAMRIAUlSjAADCcYJDkZTxYwNBUCXwM3Xgo1MAMCBAUQCj4pLW0PDyFoX0FHUVByEkZFMwIlCQUcFyZgaG0YBDExJw9HMAUmXTYAIQRlNQMAFiYhLypKBCsgeUEBBB4xRg8KO19iYFFVWGhoYW1KQWVkdQgBUTEnRgk1MAM4RCIBGTwtbywfFSoXMA0LIRUmQUYRPRIlYFFVWGhoYW1KQWVkdUFHUVB/H0Y2MAU9DwNYCyEsJG0OBCYtMQQUSlAlV0YPIAQ/ShccCi1oNSUPQTYhOQ1KEBw+Eg8DdQI4DwNVDykmNT5KAzAoPmtHUVByEkZFdVdrSlFVWGhoEygHDjEhJk8BGAI3GkQ2MBsnKx0ZKC08Mm9Da2VkdUFHUVByEkZFdRIlDntVWGhoYW1KQSAqMUhtFB42OAAQOxQ/Ax4bWAk9NSI6BDE3exITHgB6G0YkIAMkOhQBC2YXMzgEDywqMkFaURYzXhUAdRIlDnt/VWVoAiIOBDZOMxQJEgQ7XQhFFAI/BSEQDDtmMygOBCApFg4DFAN6XAkRPBEyQ3tVWGhoJyIYQRpodQIIFRVyWwhFPAcqAwMGUAsnLysDBmsHGiUiIllyVglvdVdrSlFVWGgaJCAFFSA3ewcOAxV6ECUJNB4mCxMZHQsnJShITWUnOgUCWHpyEkZFdVdrShgTWCYnNSQMGGUwPQQJUR49Rg8DLF9pKR4RHWpkYW8+EywhMVtHU1B8HEYGOhMuQ1EQFixCYW1KQWVkdUETEAM5HBEEPANjWl9BUUJoYW1KBCsgXwQJFXpYH0tFt+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3YS2BHQXxqdSwoJzUfdygxX1pmSpPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8U8oOgIGHVAfXRAAOBIlHlFIWDNoEjkLFSBkaEEce1ByEkYSNBsgOQEQHSxofG1YUWlkPxQKASA9RQMXdUprX0FZWCEmJwcfDDVkaEEBEBwhV0pFOxgoBhgFWHVoJywGEiBoX0FHUVA0Xh9FaFctCx0GHWRoJyETMjUhMAVHTFBqAkpFNBk/AzAzM2h1YTkYFCBodQkOBRI9SkZYdUVnYFFVWGg7IDsPBRUrJkFaUR47XkpvKFtrNRIaFiZofG0RHGU5X2sLHhMzXkYDIBkoHhgaFmgpMT0GGA0xOAAJHhk2Gk9vdVdrSh0aGykkYRJGQRpodQkSHFBvEjMRPBs4RBYQDAsgID9CSH5kPAdHHx8mEg4QOFc/AhQbWDotNTgYD2UhOwVtUVByEg4QOFkcCx0eKzgtJClKXGUJOhcCHBU8Rkg2IRY/D18CGSQjEj0PBCFOdUFHUQAxUwoJfRE+BBIBEScmaWRKCTApeysSHAACXREAJ1d2SjwaDi0lJCMeTxYwNBUCXxonXxY1OgAuGFEQFixhS21KQWU0NgALHVg0RwgGIR4kBFlcWCA9LGM/EiAOIAwXIR8lVxRFaFc/GAQQWC0mJWRgBCsgXwcSHxMmWwkLdTokHBQYHSY8bz4PFRIlOQo0ARU3Vk4TfFcGBQcQFS0mNWM5FSQwME8QEBw5YRYAMBNrV1EBFyY9LC8PE20yfEEIA1BgAl1FNAc7Bgg9DSUpLyIDBW1tdQQJFXo0RwgGIR4kBFE4Fz4tLCgEFWs3MBUtBB0iYgkSMAVjHFhVNSc+JCAPDzFqBhUGBRV8WBMIJSckHRQHWHVoNSIEFCgmMBNPB1lyXRRFYEdwShAFCCQxCTgHACsrPAVPWFA3XAJvMwIlCQUcFyZoDCIcBCghOxVJAhUmeg8RNxgzQgdccmhoYW0nDjMhOAQJBV4BRgcRMFkjAwUXFzBofG0eDisxOAMCA1gkG0YKJ1d5YFFVWGgkLi4LDWUbeUEPAwByD0YwIR4nGV8SHTwLKSwYSWxOdUFHURk0Eg4XJVc/AhQbWCA6MWM5CD8hdVxHJxUxRgkXZlklDwZdDmRoN2FKF2xkMA8DexU8VmwDIBkoHhgaFmgFLjsPDCAqIU8UFAQbXAAvIBo7QgdccmhoYW0nDjMhOAQJBV4BRgcRMFkiBBc/DSU4YXBKF09kdUFHGBZyREYEOxNrBB4BWAUnNygHBCswez4EHh48HA8LMz0+BwFVDCAtL0dKQWVkdUFHUT09RAMIMBk/RC4WFyYmbyQEBw8xOBFHTFAHQQMXHBk7HwUmHTo+KC4PTw8xOBE1FAEnVxURbzQkBB8QGzxgJzgEAjEtOg9PWHpyEkZFdVdrSlFVWGghJ20EDjFkGA4RFB03XBJLBgMqHhRbESYuCzgHEWUwPQQJUQI3RhMXO1cuBBV/WGhoYW1KQWVkdUFHHR8xUwpFCltrNV1VED0lYXBKNDEtORJJFhUmcQ4EJ19iYFFVWGhoYW1KQWVkdQgBURgnX0YRPRIlShkAFXILKSwEBiAXIQATFFgXXBMIez8+BxAbFyEsEjkLFSAQLBECXzonXxYMOxBiShQbHEJoYW1KQWVkdQQJFVlYEkZFdRInGRQcHmgmLjlKF2UlOwVHPB8kVwsAOwNlNRIaFiZmKCMMKzApJUETGRU8OEZFdVdrSlFVNSc+JCAPDzFqCgIIHx58WwgDHwImGksxETsrLiMEBCYwfUhcUT09RAMIMBk/RC4WFyYmbyQEBw8xOBFHTFA8WwpvdVdrShQbHEItLylgBzAqNhUOHh5yfwkTMBouBAVbCy08DyIJDSw0fRdOe1ByEkYoOgEuBxQbDGYbNSweBGsqOgILGAByD0YTX1drSlEcHmg+YSwEBWUqOhVHPB8kVwsAOwNlNRIaFiZmLyIJDSw0dRUPFB5YEkZFdVdrSlE4Fz4tLCgEFWsbNg4JH148XQUJPAdrV1EnDSYbJD8cCCYhezITFAAiVwJfFhglBBQWDGAuNCMJFSwrO0lOe1ByEkZFdVdrSlFVWCEuYSMFFWUJOhcCHBU8Rkg2IRY/D18bFyskKD1KFS0hO0EVFAQnQAhFMBkvYFFVWGhoYW1KQWVkdQ0IEhE+EgUNNAVrV1E5FyspLR0GADwhJ08kGREgUwURMAVwShgTWCYnNW0JCSQ2dRUPFB5yQAMRIAUlShQbHEJoYW1KQWVkdUFHUVA0XRRFCltrGlEcFmghMSwDEzZsNgkGA0oVVxIhMAQoDx8RGSY8MmVDSGUgOmtHUVByEkZFdVdrSlFVWGhoKCtKEX8NJiBPUzIzQQM1NAU/SFhVGSYsYT1EIiQqFg4LHRk2V0YRPRIlSgFbOykmAiIGDSwgMEFaURYzXhUAdRIlDntVWGhoYW1KQWVkdUECHxRYEkZFdVdrSlEQFixhS21KQWUhORICGBZyXAkRdQFrCx8RWAUnNygHBCswez4EHh48HAgKNhsiGlEBEC0mS21KQWVkdUFHPB8kVwsAOwNlNRIaFiZmLyIJDSw0byUOAhM9XAgANgNjQ0pVNSc+JCAPDzFqCgIIHx58XAkGOR47SkxVFiEkS21KQWUhOwVtFB42OAoKNhYnShcAFis8KCIEQTYwNBMTNxwrGk9vdVdrSh0aGykkYRJGQS02JU1HGQU/EltFAAMiBgJbHy08AiULE21tbkEOF1A8XRJFPQU7Sh4HWCYnNW0CFChkIQkCH1AgVxIQJxlrDx8RcmhoYW0GDiYlOUEFB1BvEi8LJgMqBBIQViYtNmVIIyogLDcCHR8xWxIcd15wShMDVgUpOQsFEyYhdVxHJxUxRgkXZlklDwZdSS1xbXwPWGl1MFhOSlAwREgzMBskCRgBAWh1YRsPAjErJ1JJHxUlGk9edRU9RCEUCi0mNW1XQS02JWtHUVByXgkGNBtrCBZVRWgBLz4eACsnME8JFAd6ECQKMQ4MEwMaWmFzYS8NTwglLTUIAwEnV0ZYdSEuCQUaCntmLygdSXQhbE1WFEl+AwNcfExrCBZbKGh1YXwPVX5kNwZJIREgVwgRdUprAgMFcmhoYW0nDjMhOAQJBV4NUQkLO1ktBgg3LmRoDCIcBCghOxVJLhM9XAhLMxsyKDZVRWgqN2FKAyJOdUFHURgnX0g1ORY/DB4HFRs8ICMOQXhkIRMSFHpyEkZFGBg9DxwQFjxmHi4FDytqMw0eJAA2UxIAdUprOAQbKy06NyQJBGsWMA8DFAIBRgMVJRIvUDIaFiYtIjlCBzAqNhUOHh56G2xFdVdrSlFVWCEuYSMFFWUJOhcCHBU8Rkg2IRY/D18TFDFoNSUPD2U2MBUSAx5yVwgBX1drSlFVWGhoLSIJAClkNgAKUU1yRQkXPgQ7CxIQVgs9Mz8PDzEHNAwCAxFYEkZFdVdrSlEZFyspLW0HQXhkAwQEBR8gAUgLMABjQ3tVWGhoYW1KQSwidTQUFAIbXBYQISQuGAccGy1yCD4hBDwAOhYJWTU8RwtLHhIyKR4RHWYfaG1KQWVkdUFHUQQ6VwhFOFd2ShxVU2grICBEIgM2NAwCXzw9XQ0zMBQ/BQNVHSYsS21KQWVkdUFHGBZyZxUAJz4lGgQBKy06NyQJBH8NJioCCDQ9RQhNEBk+B18+HTELLikPTxZtdUFHUVByEkZFIR8uBFEYWHVoLG1HQSYlOE8kNwIzXwNLGRgkAScQGzwnM20PDyFOdUFHUVByEkYMM1ceGRQHMSY4NDk5BDcyPAICSzkheQMcERg8BFkwFj0lbwYPGAYrMQRJMFlyEkZFdVdrSlEBEC0mYSBKXGUpdUxHEhE/HCUjJxYmD18nES8gNRsPAjErJ0ECHxRYEkZFdVdrSlEcHmgdMigYKCs0IBU0FAIkWwUAbz44IRQMPCc/L2UvDzApeyoCCDM9VgNLEV5rSlFVWGhoYW0eCSAqdQxHTFA/Ek1FNhYmRDIzCiklJGM4CCIsITcCEgQ9QEYAOxNBSlFVWGhoYW0DB2URJgQVOB4iRxI2MAU9AxIQQgE7CigTJSozO0kiHwU/HC0ALDQkDhRbKzgpIihDQWVkdUETGRU8EgtFaFcmSlpVLi0rNSIYUmsqMBZPQVxyA0pFZV5rDx8RcmhoYW1KQWVkPAdHJAM3QC8LJQI/ORQHDiErJHcjEg4hLCUIBh56dwgQOFkADwg2FywtbwEPBzEXPQgBBVlyRg4AO1cmSkxVFWhlYRsPAjErJ1JJHxUlGlZJdUZnSkFcWC0mJUdKQWVkdUFHURk0EgtLGBYsBBgBDSwtYXNKUWUwPQQJUR1yD0YIeyIlAwVVUmgFLjsPDCAqIU80BREmV0gDOQ4YGhQQHGgtLylgQWVkdUFHUVAwREgzMBskCRgBAWh1YSBgQWVkdUFHUVAwVUgmEwUqBxRVRWgrICBEIgM2NAwCe1ByEkYAOxNiYBQbHEIkLi4LDWUiIA8EBRk9XEYWIRg7LB0MUGFCYW1KQSMrJ0E4XVA5Eg8LdR47CxgHC2AzYysGGBA0MQATFFJ+EAAJLDUdSF1XHiQxAwpIHGxkMQ5tUVByEkZFdVcnBRIUFGgrYXBKLCoyMAwCHwR8bQUKOxkQASx/WGhoYW1KQWUtM0EEUQQ6VwhvdVdrSlFVWGhoYW1KCCNkIRgXFB80GgVMdUp2SlMnOhAbIj8DETEHOg8JFBMmWwkLd1c/AhQbWCtyBSQZAioqOwQEBVh7EgMJJhJrCUsxHTs8MyITSWxkMA8De1ByEkZFdVdrSlFVWAUnNygHBCswez4EHh48aQ04dUprBBgZcmhoYW1KQWVkMA8De1ByEkYAOxNBSlFVWCQnIiwGQRpodT5LURgnX0ZYdSI/Ax0GVi8tNQ4CADdsfGtHUVByWwBFPQImSgUdHSZoKTgHTxUoNBUBHgI/YRIEOxNrV1ETGSQ7JG0PDyFOMA8DexYnXAURPBglSjwaDi0lJCMeTzYhIScLCFgkG0YoOgEuBxQbDGYbNSweBGsiORhHTFAkCUYMM1c9SgUdHSZoMjkLEzECORhPWFA3XhUAdQQ/BQEzFDFgaG0PDyFkMA8DexYnXAURPBglSjwaDi0lJCMeTzYhIScLCCMiVwMBfQFiSjwaDi0lJCMeTxYwNBUCXxY+SzUVMBIvSkxVDCcmNCAIBDdsI0hHHgJyClZFMBkvYBcAFis8KCIEQQgrIwQKFB4mHBUAITYlHhg0PgNgN2RgQWVkdSwIBxU/VwgReyQ/CwUQVikmNSQrJw5kaEERe1ByEkYMM1c9ShAbHGgmLjlKLCoyMAwCHwR8bQUKOxllCx8BEQkOCm0eCSAqX0FHUVByEkZFGBg9DxwQFjxmHi4FDytqNA8TGDEUeUZYdTskCRAZKCQpOCgYTwwgOQQDSzM9XAgANgNjDAQbGzwhLiNCSE9kdUFHUVByEkZFdVciDFEbFzxoDCIcBCghOxVJIgQzRgNLNBk/AzAzM2g8KSgEQTchIRQVH1A3XAJvdVdrSlFVWGhoYW1KESYlOQ1PFwU8URIMOhljQ1EjETo8NCwGNDYhJ1skEAAmRxQAFhglHgMaFCQtM2VDWmUSPBMTBBE+ZxUAJ00IBhgWEwo9NTkFD3dsAwQEBR8gAEgLMABjQ1hVHSYsaEdKQWVkdUFHURU8Vk9vdVdrShQZCy0hJ20EDjFkI0EGHxRyfwkTMBouBAVbJysnLyNEACswPCAhOlAmWgMLX1drSlFVWGhoDCIcBCghOxVJLhM9XAhLNBk/AzAzM3IMKD4JDisqMAITWVlpEisKIxImDx8BVhcrLiMETyQqIQgmNztyD0YLPBtBSlFVWC0mJUcPDyFOMxQJEgQ7XQhFGBg9DxwQFjxmMiwcBBUrJklOe1ByEkYJOhQqBlEqVGggMz1KXGURIQgLAl41VxImPRY5QlhOWCEuYSUYEWUwPQQJUT09RAMIMBk/RCIBGTwtbz4LFyAgBQ4UUU1yWhQVeyckGRgBEScmem0YBDExJw9HBQInV0YAOxNBDx8Rci49Ly4eCCoqdSwIBxU/VwgRewUuCRAZFBgnMmVDa2VkdUEOF1AfXRAAOBIlHl8mDCk8JGMZADMhMTEIAlAmWgMLdSI/Ax0GVjwtLSgaDjcwfSwIBxU/VwgReyQ/CwUQVjspNygOMSo3fFpHAxUmRxQLdQM5HxRVHSYsSygEBU8IOgIGHSA+Ux8AJ1kIAhAHGSs8JD8rBSEhMVskHh48VwURfRE+BBIBEScmaWRgQWVkdRUGAht8RQcMIV97REdcQ2gpMT0GGA0xOAAJHhk2Gk9vdVdrShgTWAUnNygHBCswezITEAQ3HAAJLFc/AhQbWDs8ID8eJyk9fUhHFB42OEZFdVciDFE4Fz4tLCgEFWsXIQATFF46WxIHOg9rFExVSmg8KSgEQQgrIwQKFB4mHBUAIT8iHhMaAGAFLjsPDCAqIU80BREmV0gNPAMpBQlcWC0mJUcPDyFtX2tKXFCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+F/VWVocH1EQREBGSQ3PiIGYWxIeFep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N1gDSonNA1HJRU+VxYKJwM4SkxVAzVCLSIJAClkMxQJEgQ7XQhFMx4lDj8lO2AmICAPSE9kdUFHHR8xUwpFOwcoGVFIWB8nMyYZESQnMFshGB42dA8XJgMIAhgZHGBqDx0pMmdtX0FHUVA7VEYLOgNrBAEWC2g8KSgEQTchIRQVH1A8WwpFMBkvYFFVWGgmICAPQXhkOwAKFEo+XREAJ19iYFFVWGguLj9KPmlkO0EOH1A7QgcMJwRjBAEWC3IPJDkpCSwoMRMCH1h7G0YBOn1rSlFVWGhoYSQMQStqGwAKFEo+XREAJ19iUBccFixgLywHBGlkZE1HBQInV09FIR8uBHtVWGhoYW1KQWVkdUEOF1A8CC8WFF9pJx4RHSRqaG0eCSAqX0FHUVByEkZFdVdrSlFVWGghJ20ETxU2PAwGAwkCUxQRdQMjDx9VCi08ND8EQStqBRMOHBEgSzYEJwNlOh4GETwhLiNKBCsgX0FHUVByEkZFdVdrSlFVWGgkLi4LDWU0dVxHH0oUWwgBEx45GQU2ECEkJRoCCCYsHBImWVIQUxUABRY5HlNZWDw6NChDa2VkdUFHUVByEkZFdVdrSlEcHmg4YTkCBCtkJwQTBAI8EhZLBRg4AwUcFyZoJCMOa2VkdUFHUVByEkZFdRInGRQcHmgmewQZIG1mFwAUFCAzQBJHfFc/AhQbcmhoYW1KQWVkdUFHUVByEkYXMAM+GB9VFmYYLj4DFSwrO2tHUVByEkZFdVdrSlEQFixCYW1KQWVkdUECHxRYEkZFdRIlDnsQFixCLSIJAClkMxQJEgQ7XQhFMx4lDiYaCiQsaSMLDCBtX0FHUVA8UwsAdUprBBAYHXIkLjoPE21tX0FHUVA0XRRFCltrDlEcFmghMSwDEzZsAg4VGgMiUwUAbzAuHjUQCystLykLDzE3fUhOURQ9OEZFdVdrSlFVES5oJWMkACghbw0IBhUgGk9fMx4lDlkbGSUtbW1bTWUwJxQCWFAmWgMLX1drSlFVWGhoYW1KQSwidQVdOAMTGkQnNAQuOhAHDGphYTkCBCtkJwQTBAI8EgJLBRg4AwUcFyZoJCMOa2VkdUFHUVByEkZFdR4tShVPMTsJaW8nDiEhOUNOURE8VkYBeyc5AxwUCjEYID8eQTEsMA9HAxUmRxQLdRNlOgMcFSk6OB0LEzFqBQ4UGAQ7XQhFMBkvYFFVWGhoYW1KBCsgX0FHUVA3XAJvMBkvYBcAFis8KCIEQREhOQQXHgImQUgJPAQ/Qlh/WGhoYT8PFTA2O0Ece1ByEkZFdVdrEVEbGSUtYXBKQwg9dQcGAx1yGhUVNAAlQ1NZWGhoJigeQXhkMxQJEgQ7XQhNfFc5DwUACiZoBywYDGsjMBU0ARElXDYKJl9iShQbHGg1bUdKQWVkdUFHUQtyXAcIMFd2SlM4AWguID8HQW0nMA8TFAJ7EEpFdRAuHlFIWC49Ly4eCCoqfUhHAxUmRxQLdTEqGBxbHy08AigEFSA2fUhHFB42EhtJX1drSlFVWGhoOm0EACghdVxHUyM3VwJFJh8kGlE7KAtqbW1KQWVkMgQTUU1yVBMLNgMiBR9dUWg6JDkfEytkMwgJFT4CcU5HJhIuDlNcWCc6YSsDDyEKBSJPUwMzX0RMdRIlDlEIVEJoYW1KQWVkdRpHHxE/V0ZYdVUMDxAHWDsgLj1KLxUHd01HUVByEgEAIVd2ShcAFis8KCIESWxkJwQTBAI8EgAMOxMFOjJdWi8tID9ISGUrJ0EBGB42fDYmfVU/BRxXUWgtLylKHGlOdUFHUVByEkYedRkqBxRVRWhqESgeQSAjMkEUGR8iEEpFdVdrSlESHTxofG0MFCsnIQgIH1h7EhQAIQI5BFETESYsDx0pSWchMgZFWFA9QEYDPBkvJCE2UGo4JDlISGUhOwVHDFxYEkZFdVdrSlEOWCYpLChKXGVmFg4UHBUmWwVFJh8kGlNZWGhoYW0NBDFkaEEBBB4xRg8KO19iSgMQDD06L20MCCsgGzEkWVIxXRUIMAMiCVNcWC0mJW0XTU9kdUFHUVByEh1FOxYmD1FIWGobJCEGQT8rOwRFXVByEkZFdVdrShYQDGh1YSsfDyYwPA4JWVlyQAMRIAUlShccFiwfLj8GBW1mJgQLHVJ7EgMLMVc2RntVWGhoYW1KQT5kOwAKFFBvEkQxJxY9Dx0cFi9oLCgYAi0lOxVFXRc3RkZYdRE+BBIBEScmaWRKEyAwIBMJURY7XAIrBTRjSAUHGT4tLSQEBmdtdQ4VURY7XAIrBTRjSBwQCisgICMeQ2xkMA8DUQ1+OEZFdVdrSlFVA2gmICAPQXhkdywGGBwwXR5HeVdrSlFVWGhoYW1KBiAwdVxHFwU8URIMOhljQ3tVWGhoYW1KQWVkdUELHhMzXkYDdUprLBAHFWY6JD4FDTMhfUhcURk0EgBFIR8uBHtVWGhoYW1KQWVkdUFHUVByXgkGNBtrB1FIWC5yByQEBQMtJxITMhg7XgJNdzoqAx0XFzBqaEdKQWVkdUFHUVByEkZFdVdrAxdVFWgpLylKDGsUJwgKEAIrYgcXIVc/AhQbWDotNTgYD2UpezEVGB0zQB81NAU/RCEaCyE8KCIEQSAqMWtHUVByEkZFdVdrSlFVWGhoKCtKDGUwPQQJURw9UQcJdQdrV1EYQg4hLyksCDc3ISIPGBw2ZQ4MNh8CGTBdWgopMig6ADcwd01HBQInV09edR4tSgFVDCAtL20YBDExJw9HAV4CXRUMIR4kBFEQFixoJCMOa2VkdUFHUVByEkZFdRIlDntVWGhoYW1KQSAqMUEaXXpyEkZFdVdrSgpVFiklJG1XQWcDNBMDFB5ycQkMO1cYAh4FWmRoYSoPFWV5dQcSHxMmWwkLfV5rGBQBDTomYSsDDyETOhMLFVhwdQcXMRIlKR4cFmphYSgEBWU5eWtHUVByEkZFdQxrBBAYHWh1YW85BCY2MBVHPhIwS0YAOwM5E1NZWC8tNW1XQSMxOwITGB88Gk9FJxI/HwMbWC4hLyk9DjcoMUlFIhUxQAMRGhUpE1NcWC0mJW0XTU9kdUFHDHo3XAJvMwIlCQUcFyZoFSgGBDUrJxUUXxc9GggEOBJiYFFVWGguLj9KPmlkMEEOH1A7QgcMJwRjPhQZHTgnMzkZTyktJhVPWFlyVglvdVdrSlFVWGghJ20PTyslOARHTE1yXAcIMFc/AhQbcmhoYW1KQWVkdUFHURw9UQcJdQdrV1EQVi8tNWVDa2VkdUFHUVByEkZFdR4tSgFVDCAtL20/FSwoJk8TFBw3QgkXIV87SlpVLi0rNSIYUmsqMBZPQVxyBkpFZV5iUVEHHTw9MyNKFTcxMEECHxRYEkZFdVdrSlEQFixCYW1KQSAqMWtHUVByQAMRIAUlShcUFDstSygEBU9OeExHk+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbiOTlmt3Yo9j6g9DUt/T3k+XC0PP1t+LbYFxYWHl5b208KBYRFC00e11/EoTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6EIkLi4LDWUSPBISEBwhEltFLlcYHhABHWh1YTZKBzAoOQMVGBc6RkZYdREqBgIQVGgmLgsFBmV5dQcGHQM3EhtJdSgpCxIeDThofG0RHGU5Xw0IEhE+EgAQOxQ/Ax4bWCopIiYfEQktMgkTGB41Gk9vdVdrShgTWCYtOTlCNyw3IAALAl4NUAcGPgI7Q1EBEC0mYT8PFTA2O0ECHxRYEkZFdSEiGQQUFDtmHi8LAi4xJU8lAxk1WhILMAQ4SlFVWHVoDSQNCTEtOwZJMwI7VQ4ROxI4GXtVWGhoFyQZFCQoJk84ExExWRMVezQnBRIeLCElJG1KQWVkaEErGBc6Rg8LMlkIBh4WExwhLChgQWVkdTcOAgUzXhVLChUqCRoACGYPLSIIACkXPQADHgchEltFGR4sAgUcFi9mBiEFAyQoBgkGFR8lQWxFdVdrPBgGDSkkMmM1AyQnPhQXXzY9VSMLMVdrSlFVWGhofG0mCCIsIQgJFl4UXQEgOxNBSlFVWB4hMjgLDTZqCgMGEhsnQkgjOhAYHhAHDGhoYW1KQXhkGQgAGQQ7XAFLExgsOQUUCjxCJCMOayMxOwITGB88EjAMJgIqBgJbCy08BzgGDSc2PAYPBVgkG2xFdVdrPBgGDSkkMmM5FSQwME8BBBw+UBQMMh8/SkxVDnNoIywJCjA0GQgAGQQ7XAFNfH1rSlFVES5oN20eCSAqdS0OFhgmWwgCezU5AxYdDCYtMj5KXGV3bkErGBc6Rg8LMlkIBh4WExwhLChKXGV1YVpHPRk1WhIMOxBlLR0aGikkEiULBSozJkFaURYzXhUAX1drSlEQFDstS21KQWVkdUFHPRk1WhIMOxBlKAMcHyA8LygZEmV5dTcOAgUzXhVLChUqCRoACGYKMyQNCTEqMBIUUR8gEldvdVdrSlFVWGgEKCoCFSwqMk8kHR8xWTIMOBJrSkxVLiE7NCwGEmsbNwAEGgUiHCUJOhQgPhgYHWgnM21bVU9kdUFHUVByEioMMh8/Ax8SVg8kLi8LDRYsNAUIBgNyD0YzPAQ+Cx0GVhcqIC4BFDVqEg0IExE+YQ4EMRg8GVELRWguICEZBE9kdUFHFB42OAMLMX0tHx8WDCEnL208CDYxNA0UXwM3RigKExgsQgdccmhoYW08CDYxNA0UXyMmUxIAexkkLB4SWHVoN3ZKAyQnPhQXPRk1WhIMOxBjQ3tVWGhoKCtKF2UwPQQJUTw7VQ4RPBksRDcaHw0mJW1XQXQhY1pHPRk1WhIMOxBlLB4SKzwpMzlKXGV1MFdtUVByEgMJJhJrJhgSEDwhLypEJyojEA8DUU1yZA8WIBYnGV8qGikrKjgaTwMrMiQJFVA9QEZUZUd7UVE5ES8gNSQEBmsCOgY0BREgRkZYdSEiGQQUFDtmHi8LAi4xJU8hHhcBRgcXIVckGFFFWC0mJUcPDyFOX0xKUZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+pPg6Krd0a//8afRxYPy4ZLHooTwxZXe+ntYVWh5c2NKNAxkt+HzURw9UwJFGhU4AxUcGSYdKG1COHcPfEEGHxRyUBMMORNrHhkQWD8hLykFFk9peEGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOep/+GX7diq1N2I9NWmwPGF5OCwp/aHwOdBGgMcFjxgaW8xOHcPCEErHhE2WwgCdTgpGRgRESkmFCRKByo2dUQUUV58HERMbxEkGBwUDGALLiMMCCJqEiAqNC8ccysgfF5BYB0aGykkYQEDAzclJxhLUSQ6VwsAGBYlCxYQCmRoEiwcBAglOwAAFAJYXgkGNBtrBRogMWh1YT0JACkofQcSHxMmWwkLfV5BSlFVWAQhIz8LEzxkdUFHUVBvEgoKNBM4HgMcFi9gJiwHBH8MIRUXNhUmGiUKOxEiDV8gMRcaBB0lQWtqdUMrGBIgUxQcexs+C1NcUWBhS21KQWUQPQQKFD0zXAcCMAVrV1EZFyksMjkYCCsjfQYGHBVoehIRJTAuHlk2FyYuKCpENAwbByQ3PlB8HEZHNBMvBR8GVxwgJCAPLCQqNAYCA14+RwdHfF5jQ3tVWGhoEiwcBAglOwAAFAJyEltFORgqDgIBCiEmJmUNACghbykTBQAVVxJNFhglDBgSVh0BHh8vMQpke09HUxE2VgkLJlgYCwcQNSkmICoPE2soIABFWFl6G2wAOxNiYBgTWCYnNW0FChANdQ4VUR49RkYpPBU5CwMMWDwgJCNgQWVkdRYGAx56ED08ZzxrIgQXJWgOICQGBCFkIQ5HHR8zVkYqNwQiDhgUFh0hb20rAyo2IQgJFl5wG2xFdVdrNTZbIXoDHgorJhoMACM4PT8TdiMhdUprBBgZQ2g6JDkfEytOMA8De3o+XQUEOVcEGgUcFyY7bW0+DiIjOQQUUU1yfg8HJxY5E186CDwhLiMZTWUIPAMVEAIrHDIKMhAnDwJ/NCEqMywYGGsCOhMEFDM6VwUONxgzSkxVHikkMihgaykrNgALURYnXAURPBglSj8aDCEuOGUeCDEoME1HFRUhUUpFMAU5Q3tVWGhoDSQIEyQ2LFspHgQ7VB9NLn1rSlFVWGhoYRkDFSkhdUFHUVByEltFMAU5ShAbHGhgYwgYEyo2dYPn01BwEkhLdQMiHh0QUWgnM20eCDEoME1tUVByEkZFdVcPDwIWCiE4NSQFD2V5dQUCAhNyXRRFd1VnYFFVWGhoYW1KNSwpMEFHUVByEkZFaFd/RntVWGhoPGRgBCsgX2sLHhMzXkYyPBkvBQZVRWgEKC8YADc9byIVFBEmVzEMOxMkHVkOcmhoYW0+CDEoMEFHUVByEkZFdVdrSkxVWg86LjpKAGUDNBMDFB5yEoTl91drM0M+WAA9I21KF2dke09HMh88VA8CeyQIODglLBceBB9Ga2VkdUEhHh8mVxRFdVdrSlFVWGhoYXBKQxx2HkE0EgI7QhJFFxYoAUM3GSsjYW2I4edkdUNHX15ycQkLMx4sRDY0NQ0XDwwnJGlOdUFHUT49Rg8DLCQiDhRVWGhoYW1KXGVmBwgAGQRwHmxFdVdrORkaDws9MjkFDAYxJxIIA1BvEhIXIBJnYFFVWGgLJCMeBDdkdUFHUVByEkZFdUprHgMAHWRCYW1KQQQxIQ40GR8lEkZFdVdrSlFVRWg8MzgPTU9kdUFHIxUhWxwENxsuSlFVWGhoYW1XQTE2IARLe1ByEkYmOgUlDwMnGSwhND5KQWVkdVxHQEB+OBtMX30nBRIUFGgcIC8ZQXhkLmtHUVBydQcXMRIlSlFVRWgfKCMODjJ+FAUDJREwGkQiNAUvDx9XVGhoYW8ZADMhd0hLe1ByEkY2PRg7SlFVWGh1YRoDDyErIlsmFRQGUwRNdyQjBQFXVGhoYW1KQzUlNgoGFhVwG0pvdVdrSiEQDDtoYW1KQXhkAggJFR8lCCcBMSMqCFlXKC08Mm9GQWVkdUFFGRUzQBJHfFtBSlFVWBgkIDQPE2VkdVxHJhk8VgkSbzYvDiUUGmBqESELGCA2d01HUVBwRxUAJ1ViRntVWGhoDCQZAmVkdUFHTFAFWwgBOgBxKxURLCkqaW8nCDYnd01HUVByEkQSJxIlCRlXUWRCYW1KQQYrOwcOFgNyEltFAh4lDh4CQgksJRkLA21mFg4JFxk1QURJdVdpDhABGSopMihISGlOdUFHUSM3RhIMOxA4SkxVLyEmJSIdWwQgMTUGE1hwYQMRIR4lDQJXVGhqMigeFSwqMhJFWFxYEkZFdTQ5DxUcDDtoYXBKNiwqMQ4QSzE2VjIEN19pKQMQHCE8Mm9GQWVmPA8BHlJ7HmwYX31mR1GX7Miq1c2I9cVkASAlUUFy0ObxdTAKODUwNmiq1c2I9cWmweGF5fCwpuaHwfep/vGX7Miq1c2I9cWmweGF5fCwpuaHwfep/vGX7Miq1c2I9cWmweGF5fCwpuaHwfep/vGX7Miq1c2I9cWmweGF5fCwpuaHwfep/vGX7Miq1c2I9cWmweGF5fCwpuaHwfep/vGX7Miq1c2I9cWmweGF5fCwpuaHwfep/vGX7Miq1c2I9cWmweGF5fCwpuaHwfep/vGX7MhCLSIJAClkEgUJJRIqfkZYdSMqCAJbPyk6JSgEWwQgMS0CFwQGUwQHOg9jQ3sZFyspLW0tBSsUOQAJBVBvEiEBOyMpEj1POSwsFSwISWcFIBUIUSA+UwgRd15BBh4WGSRoBikEKSQ2IwQUBVBvEiEBOyMpEj1POSwsFSwISWcMNBMRFAMmEklFFhgnBhQWDGphS0ctBSsUOQAJBUoTVgIpNBUuBlkOWBwtOTlKXGVmFg4JBRk8RwkQJhsySgEZGSY8Mm0eCSBkJgQLFBMmVwJFJhIuDlEUGzonMj5KGCoxJ0EIBh43VkYDNAUmRFNZWAwnJD49EyQ0dVxHBQInV0YYfH0MDh8lFCkmNXcrBSEAPBcOFRUgGk9vEhMlOh0UFjxyACkOKCs0IBVPUyA+UwgRBhIuDj8UFS1qbW0RQREhLRVHTFBwYQMAMVclCxwQWGAtOSwJFWxmeUEjFBYzRwoRdUprSDIUCjonNW9GQRUoNAICGR8+VgMXdUprSDIUCjonNWFKMjE2NBYFFAIgS0pFe1llSF1/WGhoYRkFDikwPBFHTFBwZh8VMFc/AhRVCy0tJW0EACghdQAUURkmEgcVJRIqGAJVESZoOCIfE2UtOxcCHwQ9QB9FfQAiHhkaDTxoGh4PBCEZfE9FXXpyEkZFFhYnBhMUGyNofG0MFCsnIQgIH1gkG0YkIAMkLRAHHC0mbx4eADEhexELEB4mYQMAMVd2SgdVHSYsYTBDawQxIQ4gEAI2VwhLBgMqHhRbCCQpLzk5BCAgdVxHUzMzQBQKIVVBYDYRFhgkICMeWwQgMTUIFhc+V05HFAI/BSEZGSY8Y2FKGmUQMBkTUU1yECcQIRhrOh0UFjxoaSALEjEhJ0hFXVAWVwAEIBs/SkxVHikkMihGa2VkdUEzHh8+Rg8VdUprSCIFCi0pJT5KEiAhMRJHAxE8VgkIOQ5rCxIHFzs7YTQFFDdkMwAVHFAiXgkRe1VnYFFVWGgLICEGAyQnPkFaURYnXAURPBglQgdcWCEuYTtKFS0hO0EmBAQ9dQcXMRIlRAIBGTo8ADgeDhUoNA8TWVlyVwoWMFcKHwUaPyk6JSgETzYwOhEmBAQ9YgoEOwNjQ1EQFixoJCMOQThtXyYDHyA+UwgRbzYvDiIZESwtM2VIMSklOxUjFBwzS0RJdQxrPhQNDGh1YW86DSQqIUEOHwQ3QBAEOVVnSjUQHik9LTlKXGV0e1RLUT07XEZYdUdlW11VNSkwYXBKVGlkBw4SHxQ7XAFFaFd5RlEmDS4uKDVKXGVmdRJFXXpyEkZFARgkBgUcCGh1YW8+CCghdQMCBQc3VwhFMBYoAlEFFCkmNWNITU9kdUFHMhE+XgQENhxrV1ETDSYrNSQFD20yfEEmBAQ9dQcXMRIlRCIBGTwtbz0GACswEQQLEAlyD0YTdRIlDlEIUUIPJSM6DSQqIVsmFRQGXQECORJjSDscDDwtM29GQT5kAQQfBVBvEkQ3NBkvBRwcAi1oNSQHCCsjJkNLUTQ3VAcQOQNrV1EBCj0tbUdKQWVkAQ4IHQQ7QkZYdVUKDhUGWIr5cH9PQTclOwUIHB43QRVFJhhrHhkQWDgpNTkPEytkPBIJVgRyQgMXMxIoHh0MWDonIyIeCCZqd01tUVByEiUEORspCxIeWHVoJzgEAjEtOg9PB1lycxMROjAqGBUQFmYbNSweBGsuPBUTFAJyD0YTdRIlDlEIUUJCBikEKSQ2IwQUBUoTVgIpNBUuBlkOWBwtOTlKXGVmFBQTHl06UxQTMAQ/SgMcCC1oMSELDzE3dQAJFVAlUwoOdRg9DwNVHDonMT0PBWUiJxQOBVAmXUYVPBQgShgBWD04b29GQQErMBIwAxEiEltFIQU+D1EIUUIPJSMiADcyMBITSzE2ViIMIx4vDwNdUUIPJSMiADcyMBITSzE2VjIKMhAnD1lXOT08LgULEzMhJhVFXVApEjIALQNrV1FXOT08Lm0iADcyMBITUQA+UwgRJlVnSjUQHik9LTlKXGUiNA0UFFxYEkZFdSMkBR0BEThofG1IIiQoORJHBRg3Eg4EJwEuGQVVCi0lLjkPQSoqdQQRFAIrEhYJNBk/Sh4bWDEnND9KByQ2OE9FXXpyEkZFFhYnBhMUGyNofG0MFCsnIQgIH1gkG0YMM1c9SgUdHSZoADgeDgIlJwUCH14hRgcXITY+Hh49GTo+JD4eSWxkMA0UFFATRxIKEhY5DhQbVjs8Lj0rFDErHQAVBxUhRk5MdRIlDlEQFixoPGRgJiEqHQAVBxUhRlwkMRMYBhgRHTpgYwULEzMhJhUuHwQ3QBAEOVVnSgpVLC0wNW1XQWcMNBMRFAMmEg8LIRI5HBAZWmRoBSgMADAoIUFaUUN+EisMO1d2SkBZWAUpOW1XQXN0eUE1HgU8Vg8LMld2SkBZWBs9JysDGWV5dUNHAlJ+OEZFdVcICx0ZGikrKm1XQSMxOwITGB88GhBMdTY+Hh4yGTosJCNEMjElIQRJGREgRAMWIT4lHhQHDikkYXBKF2UhOwVHDFlYdQILHRY5HBQGDHIJJSkuCDMtMQQVWVlYdQILHRY5HBQGDHIJJSk+DiIjOQRPUzEnRgkmOhsnDxIBWmRoOm0+BD0wdVxHUzEnRglFAhYnAVw2FyQkJC4eQTctJQRFXVAWVwAEIBs/SkxVHikkMihGa2VkdUEzHh8+Rg8VdUprSCYUFCM7YSIcBDdkMAAEGVAgWxYAdRE5HxgBWDsnYSQeQSQxIQ5KARkxWRVFIAdlSF1/WGhoYQ4LDSkmNAIMUU1yVBMLNgMiBR9dDmFoKCtKF2UwPQQJUTEnRgkiNAUvDx9bCzwpMzkrFDErFg4LHRUxRk5MdRInGRRVOT08LgoLEyEhO08UBR8icxMROjQkBh0QGzxgaG0PDyFkMA8DUQ17OCEBOz8qGAcQCzxyACkOMiktMQQVWVIRXQoJMBQ/Ix8BHTo+ICFITWU/dTUCCQRyD0ZHFhgnBhQWDGghLzkPEzMlOUNLUTQ3VAcQOQNrV1FBVGgFKCNKXGV1eUEqEAhyD0ZTZVtrOB4AFiwhLypKXGV1eUE0BBY0Wx5FaFdpSgJXVEJoYW1KIiQoOQMGEhtyD0YDIBkoHhgaFmA+aG0rFDErEgAVFRU8HDURNAMuRBIaFCQtIjkjDzEhJxcGHVBvEhBFMBkvSgxcckIkLi4LDWUDMQ8zEwgAEltFARYpGV8yGTosJCNQICEgBwgAGQQGUwQHOg9jQ3sZFyspLW0tBSsXMA0LUU1ydQILARUzOEs0HCwcIC9CQxYhOQ1HXlAFUxIAJ1ViYB0aGykkYQoODxYwNBUUUU1ydQILARUzOEs0HCwcIC9CQwktIwRHEh8nXBIAJwRpQ3t/PywmEigGDX8FMQUrEBI3Xk4edSMuEgVVRWhqADgeDmg3MA0LAlA6VwoBdREkBRVVGSYsYToLFSA2JkEGHRxySwkQJ1c7BhAbDDtoLiNKFSwpMBMUX1J+EiIKMAQcGBAFWHVoNT8fBGU5fGsgFR4BVwoJbzYvDjUcDiEsJD9CSE8DMQ80FBw+CCcBMSMkDRYZHWBqADgeDhYhOQ1FXVApEjIALQNrV1FXOT08Lm05BCkodQcIHhRwHkYhMBEqHx0BWHVoJywGEiBoX0FHUVAGXQkJIR47SkxVWg4hMygZQTEsMEEUFBw+EhQAOBg/D19VKzwpLylKDyAlJ0ETGRVyYQMJOVcFOjJbWmRCYW1KQQYlOQ0FEBM5EltFMwIlCQUcFyZgN2RKCCNkI0ETGRU8EicQIRgMCwMRHSZmMjkLEzEFIBUIIhU+Xk5MdRInGRRVOT08LgoLEyEhO08UBR8icxMROiQuBh1dUWgtLylKBCsgdRxOezc2XDUAORtxKxURKyQhJSgYSWcXMA0LOB4mVxQTNBtpRlEOWBwtOTlKXGVmBgQLHVA7XBIAJwEqBlNZWAwtJywfDTFkaEFUQVxyfw8LdUprX11VNSkwYXBKV3V0eUE1HgU8Vg8LMld2SkFZWBs9JysDGWV5dUNHAlJ+OEZFdVcICx0ZGikrKm1XQSMxOwITGB88GhBMdTY+Hh4yGTosJCNEMjElIQRJAhU+Xi8LIRI5HBAZWHVoN20PDyFkKEhtNhQ8YQMJOU0KDhUxET4hJSgYSWxOEgUJIhU+XlwkMRMfBRYSFC1gYwwfFSoTNBUCA1J+Eh1FARIzHlFIWGoJNDkFQRIlIQQVURczQAIAOwRpRlExHS4pNCEeQXhkMwALAhV+OEZFdVcfBR4ZDCE4YXBKQwYlOQ0UUQQ6V0YyNAMuGCgaDToPID8OBCs3dRMCHB8mV0hFFxgkGQUGWC86LjoeCWtmeWtHUVBycQcJORUqCRpVRWguNCMJFSwrO0kRWFA7VEYTdQMjDx9VOT08LgoLEyEhO08UBREgRicQIRgcCwUQCmBhYSgGEiBkFBQTHjczQAIAO1k4Hh4FOT08LhoLFSA2fUhHFB42EgMLMVc2Q3syHCYbJCEGWwQgMTILGBQ3QE5HAhY/DwM8FjwtMzsLDWdodRpHJRUqRkZYdVUcCwUQCmghLzkPEzMlOUNLUTQ3VAcQOQNrV1FDSGRoDCQEQXhkZFFLUT0zSkZYdUF7Wl1VKic9LykDDyJkaEFXXVABRwADPA9rV1FXWDtqbUdKQWVkFgALHRIzUQ1FaFctHx8WDCEnL2UcSGUFIBUINhEgVgMLeyQ/CwUQVj8pNSgYKCswMBMREBxyD0YTdRIlDlEIUUIPJSM5BCkobyADFTQ7RA8BMAVjQ3syHCYbJCEGWwQgMSMSBQQ9XE4edSMuEgVVRWhqEigGDWUiOg4DUT4dZURJdTE+BBJVRWguNCMJFSwrO0lOUSI3XwkRMARlDBgHHWBqEigGDQMrOgVFWEtyfAkRPBEyQlMmHSQkY2FKQwMtJwQDX1J7EgMLMVc2Q3syHCYbJCEGWwQgMSMSBQQ9XE4edSMuEgVVRWhqFiweBDdkGy4wU1xyEkZFdTE+BBJVRWguNCMJFSwrO0lOUSI3XwkRMARlAx8DFyMtaW89ADEhJyYGAxQ3XBVHfExrJB4BES4xaW89ADEhJ0NLUVIUWxQAMVlpQ1EQFixoPGRgaykrNgALURwwXjYJNBk/DxVVWGh1YQoODxYwNBUUSzE2VioENxInQlMlFCkmNSgOQWVkb0FXU1lYXgkGNBtrBhMZMCk6NygZFSAgdVxHNhQ8YRIEIQRxKxURNCkqJCFCQw0lJxcCAgQ3VkZfdUdpQ3sZFyspLW0GAykGOhQAGQRyEkZFaFcMDh8mDCk8MncrBSEINAMCHVhwYQ4KJVcpHwgGWHJocW9DaykrNgALURwwXjUKORNrSlFVWGh1YQoODxYwNBUUSzE2VioENxInQlMmHSQkYS4LDSk3b0FXU1lYXgkGNBtrBhMZLTg8KCAPQWVkdVxHNhQ8YRIEIQRxKxURNCkqJCFCQxA0IQgKFFByEkZfdUd7UEFFQnh4Y2RgJiEqBhUGBQNocwIBER49AxUQCmBhSwoODxYwNBUUSzE2ViQQIQMkBFkOWBwtOTlKXGVmBwQUFARyQRIEIQRpRlEzDSYrYXBKBzAqNhUOHh56G0Y2IRY/GV8HHTstNWVDWmUKOhUOFwl6EDURNAM4SF1VWhotMigeT2dtdQQJFVAvG2xveFpriOX1mtzIo9nqQREFF0FVUZLSpkY2HTgbSpPh+Krcwa/+4afQ1YPz8ZLGsoTx1ZXf6pPh+Krcwa/+4afQ1YPz8ZLGsoTx1ZXf6pPh+Krcwa/+4afQ1YPz8ZLGsoTx1ZXf6pPh+Krcwa/+4afQ1YPz8ZLGsoTx1ZXf6pPh+Krcwa/+4afQ1YPz8ZLGsoTx1ZXf6pPh+Krcwa/+4afQ1YPz8ZLGsoTx1ZXf6pPh+Krcwa/+4afQ1YPz8ZLGsoTx1ZXf6pPh+KrcwUcGDiYlOUE0GQAGUB4pdUprPhAXC2YbKSIaWwQgMS0CFwQGUwQHOg9jQ3sZFyspLW05CTUXMAQDAlBvEjUNJSMpEj1POSwsFSwISWcXMAQDAlB0EiEANAVpQ3sZFyspLW05CTUBMgYUUVBvEjUNJSMpEj1POSwsFSwISWcBMgYUUVZydxAAOwM4SFh/chsgMR4PBCE3byADFTwzUAMJfQxrPhQNDGh1YW8rFDEreAMSCANyQQMAMVcqBBVVHy0pM20ZCSo0dRITHhM5EgkLdRZrHhgYHTpmYQwOBWUnOgwKEF0hVxYEJxY/DxVVFiklJD5EQ2lkEQ4CAicgUxZFaFc/GAQQWDVhSx4CERYhMAUUSzE2ViIMIx4vDwNdUUIbKT05BCAgJlsmFRQbXBYQIV9pORQQHAYpLCgZQ2lkLkEzFAgmEltFdyQuDxUGWDwnYS8fGGdodSUCFxEnXhJFaFdpKRAHCic8bR4eEyQzNwQVAwl+cAoQMBUuGAMMVBwnLCweDmdoX0FHUVACXgcGMB8kBhUQCmh1YW8JDigpNEwUFAAzQAcRMBNrBBAYHTtqbUdKQWVkAQ4IHQQ7QkZYdVUIBRwYGWU7JD0LEyQwMAVHHRkhRkYKM1c4DxQRWCYpLCgZQTErdRESAxM6UxUAdQAjDx9VESZoMjkFAi5qd01tUVByEiUEORspCxIeWHVoJzgEAjEtOg9PB1lYEkZFdVdrSlE0DTwnEiUFEWsXIQATFF4hVwMBGxYmDwJVRWgzPEdKQWVkdUFHURY9QEYLdR4lSgUaCzw6KCMNSTNtbwYKEAQxWk5HDilnN1pXUWgsLkdKQWVkdUFHUVByEkYJOhQqBlEGWHVoL3cHADEnPUlFL1UhGE5LeF5uGVtRWmFCYW1KQWVkdUFHUVByWwBFJlc1V1FXWmg8KSgEQTElNw0CXxk8QQMXIV8KHwUaKyAnMWM5FSQwME8UFBU2fAcIMARnSgJcWC0mJUdKQWVkdUFHURU8VmxFdVdrDx8RWDVhSx4CERYhMAUUSzE2VjIKMhAnD1lXOT08Lg8fGBYhMAUUU1xySUYxMA8/SkxVWgk9NSJKIzA9dRICFBQhEEpFERItCwQZDGh1YSsLDTYheWtHUVBycQcJORUqCRpVRWguNCMJFSwrO0kRWFATRxIKBh8kGl8mDCk8JGMLFDErBgQCFQNyD0YTblciDFEDWDwgJCNKIDAwOjIPHgB8QRIEJwNjQ1EQFixoJCMOQThtXzIPASM3VwIWbzYvDjUcDiEsJD9CSE8XPRE0FBU2QVwkMRMCBAEADGBqBigLEwslOAQUU1xySUYxMA8/SkxVWg8tID9KFSpkNxQeU1xydgMDNAInHlFIWGofIDkPEywqMkEkEB5+ZhQKIhInSF1/WGhoYR0GACYhPQ4LFRUgEltFdxQkBxwUVTstMSwYADEhMUEJEB03QURJX1drSlE2GSQkIywJCmV5dQcSHxMmWwkLfQFiYFFVWGhoYW1KIDAwOjIPHgB8YRIEIRJlDRQUCgYpLCgZQXhkLhxtUVByEkZFdVctBQNVFmghL20eDjYwJwgJFlgkG1wCOBY/CRldWhMWbRBBQ2xkMQ5tUVByEkZFdVdrSlFVFCcrICFKEmV5dQ9dHBEmUQ5NdyluGVtdVmVhZD5ARWdtX0FHUVByEkZFdVdrShgTWDtoP3BKQ2dkIQkCH1AmUwQJMFkiBAIQCjxgADgeDhYsOhFJIgQzRgNLMhIqGD8UFS07bW0ZSGUhOwVtUVByEkZFdVcuBBV/WGhoYSgEBWU5fGs0GQABVwMBJk0KDhUhFy8vLShCQwQxIQ4lBAkVVwcXd1trEVEhHTA8YXBKQwQxIQ5HMwUrEgEANAVpRlExHS4pNCEeQXhkMwALAhV+OEZFdVcICx0ZGikrKm1XQSMxOwITGB88GhBMdTY+Hh4mECc4bx4eADEhewASBR8VVwcXdUprHEpVES5oN20eCSAqdSASBR8BWgkVewQ/CwMBUGFoJCMOQSAqMUEaWHoBWhY2MBIvGUs0HCwMKDsDBSA2fUhtIhgiYQMAMQRxKxURKyQhJSgYSWcXPQ4XOB4mVxQTNBtpRlEOWBwtOTlKXGVmBgkIAVAxWgMGPlciBAUQCj4pLW9GQQEhMwASHQRyD0ZQeVcGAx9VRWh5bW0nAD1kaEFRQVxyYAkQOxMiBBZVRWh5bW05FCMiPBlHTFBwEhVHeX1rSlFVOykkLS8LAi5kaEEBBB4xRg8KO189Q1E0DTwnEiUFEWsXIQATFF47XBIAJwEqBlFIWD5oJCMOQThtX2s0GQAXVQEWbzYvDj0UGi0kaTZKNSA8IUFaUVITRxIKeBU+EwJVCC08YSgNBjZkNA8DUQQgWwECMAU4ShQDHSY8biMDBi0wehUVEAY3Xg8LMlomDwMWECkmNW0ZCSo0Jk9FXVAWXQMWAgUqGlFIWDw6NChKHGxOBgkXNBc1QVwkMRMPAwccHC06aWRgMi00EAYAAkoTVgIsOwc+HllXPS8vDywHBDZmeUEcUSQ3ShJFaFdpLxYSC2g8Lm0IFDxmeUEjFBYzRwoRdUprSDIaFSUnL20vBiJmeWtHUVByYgoENhIjBR0RHTpofG1IAiopOABKAhUiUxQEIRIvShQSH2gmICAPEmdoX0FHUVARUwoJNxYoAVFIWC49Ly4eCCoqfRdOe1ByEkZFdVdrKwQBFxsgLj1EMjElIQRJFBc1fAcIMARrV1EOBUJoYW1KQWVkdQcIA1A8Eg8LdQMkGQUHESYvaTtDWyIpNBUEGVhwaThJCFxpQ1ERF0JoYW1KQWVkdUFHUVA+XQUEOVc4SkxVFnIlIDkJCW1mC0QUW1h8H09AJl1vSFh/WGhoYW1KQWVkdUFHGBZyQUYbaFdpSFEBEC0mYTkLAykhewgJAhUgRk4kIAMkORkaCGYbNSweBGshMgYpEB03QUpFJl5rDx8RcmhoYW1KQWVkMA8De1ByEkYAOxNrF1h/KyA4BCoNEn8FMQUzHhc1XgNNdzY+Hh43DTENJioZQ2lkLkEzFAgmEltFdzY+Hh5VOj0xYSgNBjZmeUEjFBYzRwoRdUprDBAZCy1kS21KQWUHNA0LExExWUZYdRE+BBIBEScmaTtDQQQxIQ40GR8iHDURNAMuRBAADCcNJioZQXhkI1pHGBZyREYRPRIlSjAADCcbKSIaTzYwNBMTWVlyVwgBdRIlDlEIUUIbKT0vBiI3byADFTQ7RA8BMAVjQ3smEDgNJioZWwQgMTUIFhc+V05HEAEuBAUmECc4Y2FKGmUQMBkTUU1yECcQIRhrKAQMWA0+JCMeQTYsOhFFXVAWVwAEIBs/SkxVHikkMihGa2VkdUEzHh8+Rg8VdUprSDMAATtoJDsPDzFpJgkIAVAhRgkGPldtSjQUCzwtM20ZFSonPkEQGRU8EgcGIR49D19XVEJoYW1KIiQoOQMGEhtyD0YDIBkoHhgaFmA+aG0rFDErBgkIAV4BRgcRMFkuHBQbDBsgLj1KXGUybkEOF1AkEhINMBlrKwQBFxsgLj1EEjElJxVPWFA3XAJFMBkvSgxcchsgMQgNBjZ+FAUDJR81VQoAfVUFAxYdDBsgLj1ITWU/dTUCCQRyD0ZHFAI/BVE3DTFoDyQNCTFkJgkIAVJ+EiIAMxY+BgVVRWguICEZBGlOdUFHUTMzXgoHNBQgSkxVHj0mIjkDDitsI0hHMAUmXTUNOgdlOQUUDC1mLyQNCTFkaEERSlA7VEYTdQMjDx9VOT08Lh4CDjVqJhUGAwR6G0YAOxNrDx8RWDVhSx4CEQAjMhJdMBQ2ZgkCMhsuQlMhCik+JCEDDyIJMBMEGVJ+Eh1FARIzHlFIWGoJNDkFQQcxLEEzAxEkVwoMOxBrJxQHGyApLzlITWUAMAcGBBwmEltFMxYnGRRZcmhoYW0pACkoNwAEGlBvEgAQOxQ/Ax4bUD5hYQwfFSoXPQ4XXyMmUxIAewM5CwcQFCEmJm1XQTN/dQgBUQZyRg4AO1cKHwUaKyAnMWMZFSQ2IUlOURU8VkYAOxNrF1h/ciQnIiwGQRYsJTNHTFAGUwQWeyQjBQFPOSwsEyQNCTEDJw4SARI9Sk5HBAIiCRpVGSs8KCIEEmdodUMMFAlwG2w2PQcZUDARHAQpIygGST5kAQQfBVBvEkQoNBk+Cx1VFyYtbD4CDjFkJgkIAVAzURIMOhk4RFNZWAwnJD49EyQ0dVxHBQInV0YYfH0YAgEnQgksJQkDFywgMBNPWHoBWhY3bzYvDjMADDwnL2URQREhLRVHTFBwcBMcdTYHJlEGHS0sMm1CBzcrOEELGAMmG0RJdTE+BBJVRWguNCMJFSwrO0lOe1ByEkYDOgVrNV1VFmghL20DESQtJxJPMAUmXTUNOgdlOQUUDC1mMigPBQslOAQUWFA2XUY3MBokHhQGVi4hMyhCQwcxLDICFBRwHkYLfExrHhAGE2Y/ICQeSXVqZEhHFB42OEZFdVcFBQUcHjFgYx4CDjVmeUFFJQI7VwJFNwIyAx8SWDstJCkZT2dtXwQJFVAvG2w2PQcZUDARHAo9NTkFD20/dTUCCQRyD0ZHFwIySjA5NGgvJCwYQW0iJw4KURw7QRJMd1trLAQbG2h1YSsfDyYwPA4JWVlYEkZFdREkGFEqVGgmYSQEQSw0NAgVAlgTRxIKBh8kGl8mDCk8JGMNBCQ2GwAKFAN7EgIKdSUuBx4BHTtmJyQYBG1mFxQeNhUzQERJdRliUVEBGTsjbzoLCDFsZU9WWFA3XAJvdVdrSj8aDCEuOGVIMi0rJUNLUVIGQA8AMVcpHwgcFi9oJigLE2tmfGsCHxRyT09vBh87OEs0HCwKNDkeDitsLkEzFAgmEltFdzU+E1E0NARoJCoNEmVsMxMIHFA+WxURfFVnSjcAFitofG0MFCsnIQgIH1h7OEZFdVctBQNVJ2RoL20DD2UtJQAOAwN6cxMROiQjBQFbKzwpNShEBCIjGwAKFAN7EgIKdSUuBx4BHTtmJyQYBG1mFxQeIRUmdwECd1trBFhOWDwpMiZEFiQtIUlXX0F7EgMLMX1rSlFVNic8KCsTSWcXPQ4XU1xyEDIXPBIvShMAASEmJm0PBiI3e0NOexU8VkYYfH0YAgEnQgksJQkDFywgMBNPWHoBWhY3bzYvDjMADDwnL2URQREhLRVHTFBwYAMBMBImSjA5NGgqNCQGFWgtO0EEHhQ3QURJX1drSlEhFyckNSQaQXhkdzUVGBUhEgMTMAUyShobFz8mYSwJFSwyMEEEHhQ3EgAXOhprHhkQWCo9KCEeTCwqdQ0OAgR8EEpvdVdrSjcAFitofG0MFCsnIQgIH1h7EicQIRgbDwUGVjotJSgPDAYrMQQUWT49Rg8DLF5rDx8RWDVhSx4CERd+FAUDOB4iRxJNdzQ+GQUaFQsnJShITWU/dTUCCQRyD0ZHFgI4Hh4YWCsnJShITWUAMAcGBBwmEltFd1VnSiEZGSstKSIGBSA2dVxHUyQrQgNFNFcoBRUQVmZmY2FKIiQoOQMGEhtyD0YDIBkoHhgaFmBhYSgEBWU5fGs0GQAACCcBMTU+HgUaFmAzYRkPGTFkaEFFIxU2VwMIdRQ+GQUaFWgrLikPQ2lkExQJElBvEgAQOxQ/Ax4bUGFCYW1KQSkrNgALURM9VgNFaFcEGgUcFyY7bw4fEjErOCIIFRVyUwgBdTg7HhgaFjtmAjgZFSopFg4DFF4EUwoQMFckGFFXWkJoYW1KCCNkNg4DFFBvD0ZHd1c/AhQbWAYnNSQMGG1mFg4DFFJ+EkQgOAc/E1NZWDw6NChDWmU2MBUSAx5yVwgBX1drSlEnHSUnNSgZTyMtJwRPUzM+Uw8INBUnDzIaHC1qbW0JDiEhfFpHPx8mWwAcfVUIBRUQWmRoYxkYCCAgb0FFUV58EgUKMRJiYBQbHGg1aEdgTGhkt/Xnk+TS0PLldSMKKFFGWKrI1W06JBEXdYPz8ZLGsoTx1ZXf6pPh+Krcwa/+4afQ1YPz8ZLGsoTx1ZXf6pPh+Krcwa/+4afQ1YPz8ZLGsoTx1ZXf6pPh+Krcwa/+4afQ1YPz8ZLGsoTx1ZXf6pPh+Krcwa/+4afQ1YPz8ZLGsoTx1ZXf6pPh+Krcwa/+4afQ1YPz8ZLGsoTx1ZXf6pPh+Krcwa/+4afQ1YPz8ZLGsoTx1ZXf6pPh+Krcwa/+4afQ1YPz8ZLGsmwJOhQqBlElHTwEYXBKNSQmJk83FAQhCCcBMTsuDAUyCic9MS8FGW1mBgQLHVB0EisEOxYsD1NZWGogJCwYFWdtXzECBTxocwIBGRYpDx1dA2gcJDUeQXhkdzICHRxyQgMRJlciBFEXDSQjYSIYQSoqMEwUGR8mHEYnMFcoCwMQHj0kYToDFS1kBgQLHVATfipEd1trLh4QCx86ID1KXGUwJxQCUQ17ODYAITtxKxURPCE+KCkPE21tXzECBTxocwIBARgsDR0QUGoJNDkFMiAoOTECBQNwHkYedSMuEgVVRWhqADgeDmUXMA0LUTEefkY1MAM4SlkZFyc4aG9GQQEhMwASHQRyD0YDNBs4D11VKiE7KjRKXGUwJxQCXXpyEkZFARgkBgUcCGh1YW86BDctOgUOEhE+Xh9FMx45DwJVKy0kLQwGDRUhIRJJUSUhV0YSPAMjShIUCi1mY2FgQWVkdSIGHRwwUwUOdUprDAQbGzwhLiNCF2xkFBQTHiA3RhVLBgMqHhRbGT08Lh4PDSkUMBUUUU1yRF1FPBFrHFEBEC0mYQwfFSoUMBUUXwMmUxQRfV5rDx8RWC0mJW0XSE8UMBUrSzE2VjUJPBMuGFlXKy0kLR0PFQwqIQQVBxE+EEpFLlcfDwkBWHVoYx4PDSlpJQQTURk8RgMXIxYnSF1VPC0uIDgGFWV5dVJXXVAfWwhFaFd+RlE4GTBofG1cUXVodTMIBB42WwgCdUprWl1VKz0uJyQSQXhkd0EUU1xYEkZFdTQqBh0XGSsjYXBKBzAqNhUOHh56RE9FFAI/BSEQDDtmEjkLFSBqJgQLHSA3Ri8LIRI5HBAZWHVoN20PDyFkKEhtIRUmflwkMRMPAwccHC06aWRgMSAwGVsmFRQQRxIROhljEVEhHTA8YXBKQxYhOQ1HMDweEhYAIQRrJD4iWmRoBSIfAykhFg0OEhtyD0YRJwIuRntVWGhoFSIFDTEtJUFaUVIdXANIJh8kHlEmHSQkYQwmLWtkEQ4SExw3HwUJPBQgSgUaWCsnLysDEyhqd01tUVByEiAQOxRrV1ETDSYrNSQFD21tdSASBR8CVxIWewQuBh00FCRgaHZKLyowPAceWVICVxIWd1trSCIQFCQJLSFKByw2MAVJU1lyVwgBdQpiYHsZFyspLW06BDEWdVxHJREwQUg1MAM4UDARHBohJiUeJjcrIBEFHgh6ECMUIB47SldVOicnMjlITWVmPgQeU1lYYgMRB00KDhU5GSotLWURQREhLRVHTFBwfwcLIBYnSgEQDGgtMDgDETZkNA8DURI9XRURdQM5AxYSHTo7YWUoBCBkFg4LHh4rHkYoIAMqHhgaFmgFIC4CCCsheUECBRN7HERJdTMkDwIiCik4YXBKFTcxMEEaWHoCVxI3bzYvDjUcDiEsJD9CSE8UMBU1SzE2ViQQIQMkBFkOWBwtOTlKXGVmARMOFhc3QEYoIAMqHhgaFmgFIC4CCCshd01HNwU8UUZYdRE+BBIBEScmaWRKMyApOhUCAl40WxQAfVUbDwU4DTwpNSQFDwglNgkOHxUBVxQTPBQuNSMwWmFoJCMOQThtXzECBSJocwIBFwI/Hh4bUDNoFSgSFWV5dUMyAhVyYgMRdSckHxIdWmRoYW1KQWVkdUFHUVAURwgGdUprDAQbGzwhLiNCSGUWMAwIBRUhHAAMJxJjSCEQDBgnNC4CNDYhd0hHFB42EhtMXycuHiNPOSwsAzgeFSoqfRpHJRUqRkZYdVUeGRRVPikhMzRKLyAwd01HUVByEkZFdVdrSlEzDSYrYXBKBzAqNhUOHh56G0Y3MBokHhQGVi4hMyhCQwMlPBMePxUmcwURPAEqHhQRWmFoJCMOQThtXzECBSJocwIBFwI/Hh4bUDNoFSgSFWV5dUMyAhVydAcMJw5rOQQYFScmJD9ITWVkdUFHUVAURwgGdUprDAQbGzwhLiNCSGUWMAwIBRUhHAAMJxJjSDcUEToxEjgHDCoqMBMmEgQ7RAcRMBNpQ1EQFixoPGRgMSAwB1smFRQQRxIROhljEVEhHTA8YXBKQxA3MEE3FARyfAcIMFcZDwMaFCQtM29GQWVkdScSHxNyD0YDIBkoHhgaFmBhYR8PDCowMBJJFxkgV05HBRI/JBAYHRotMyIGDSA2FAITGAYzRgMBd15rDx8RWDVhS0dHTGWmweGF5fCwpuZFATYJSkVVmsjcYR0mIBwBB0GF5fCwpuaHwfep/vGX7Miq1c2I9cWmweGF5fCwpuaHwfep/vGX7Miq1c2I9cWmweGF5fCwpuaHwfep/vGX7Miq1c2I9cWmweGF5fCwpuaHwfep/vGX7Miq1c2I9cWmweGF5fCwpuaHwfep/vGX7Miq1c2I9cWmweGF5fCwpuaHwfep/vGX7Miq1c2I9cWmweGF5fCwpuaHwfep/vGX7Miq1c2I9cWmweFtHR8xUwpFBRs5PhMNNGh1YRkLAzZqBQ0GCBUgCCcBMTsuDAUhGSoqLjVCSE8oOgIGHVAfXRAAARYpSkxVKCQ6FS8SLX8FMQUzEBJ6ECsKIxImDx8BWmFCLSIJAClkAwgUJREwEkZYdScnGCUXAARyACkONSQmfUMxGAMnUwoWd15BYDwaDi0cIC9QICEgGQAFFBx6SUYxMA8/SkxVWhs4JCgOTWUuIAwXURE8VkYIOgEuBxQbDGggJCEaBDc3e0E1FF0zQhYJPBI4Sh4bWDotMj0LFitqd01HNR83QTEXNAdrV1EBCj0tYTBDawgrIwQzEBJocwIBER49AxUQCmBhSwAFFyAQNANdMBQ2YQoMMRI5QlMiGSQjEj0PBCFmeUEcUSQ3ShJFaFdpPRAZE2gbMSgPBWdodSUCFxEnXhJFaFd5Wl1VNSEmYXBKUHNodSwGCVBvElRVZVtrOB4AFiwhLypKXGV0eUE0BBY0Wx5FaFdpSgIBDSw7bj5ITU9kdUFHJR89XhIMJVd2SlMyGSUtYSkPByQxORVHGANyAFZLd1trKRAZFCopIiZKXGUJOhcCHBU8RkgWMAMcCx0eKzgtJClKHGxOGA4RFCQzUFwkMRMYBhgRHTpgYwcfDDUUOhYCA1J+Eh1FARIzHlFIWGoCNCAaQRUrIgQVU1xydgMDNAInHlFIWH14bW0nCCtkaEFSQVxyfwcddUprWUFFVGgaLjgEBSwqMkFaUUB+EiUEORspCxIeWHVoDCIcBCghOxVJAhUmeBMIJSckHRQHWDVhSwAFFyAQNANdMBQ2ZgkCMhsuQlM8Fi4CNCAaQ2lkdUEcUSQ3ShJFaFdpIx8TESYhNShKKzApJUNLUTQ3VAcQOQNrV1ETGSQ7JGFKIiQoOQMGEhtyD0YoOgEuBxQbDGY7JDkjDyMOIAwXUQ17OCsKIxIfCxNPOSwsFSINBikhfUMpHhM+WxZHeVdrSlEOWBwtOTlKXGVmGw4EHRkiEEpFdVdrSlFVWAwtJywfDTFkaEEBEBwhV0pFFhYnBhMUGyNofG0nDjMhOAQJBV4hVxIrOhQnAwFVBWFCDCIcBBElN1smFRQWWxAMMRI5Qlh/NSc+JBkLA38FMQUzHhc1XgNNdzEnE1NZWGhoYW1KQT5kAQQfBVBvEkQjOQ5pRlExHS4pNCEeQXhkMwALAhV+EjIKOhs/AwFVRWhqFgw5JWVvdTIXEBM3HSo2PR4tHlNZWAspLSEIACYvdVxHPB8kVwsAOwNlGRQBPiQxYTBDawgrIwQzEBJocwIBBhsiDhQHUGoOLTQ5ESAhMUNLUVApEjIALQNrV1FXPiQxYR4aBCAgd01HNRU0UxMJIVd2SklFVGgFKCNKXGV1ZU1HPBEqEltFYUd7RlEnFz0mJSQEBmV5dVFLUTMzXgoHNBQgSkxVNSc+JCAPDzFqJgQTNxwrYRYAMBNrF1h/NSc+JBkLA38FMQUjGAY7VgMXfV5BJx4DHRwpI3crBSEQOgYAHRV6ECcLIR4KLDpXVGhoYTZKNSA8IUFaUVITXBIMeDYNIVNZWAwtJywfDTFkaEETAwU3HkYxOhgnHhgFWHVoYw8GDiYvJkETGRVyAFZIOB4lShgRFC1oKiQJCmtmeUEkEBw+UAcGPld2SjwaDi0lJCMeTzYhISAJBRkTdC1FKF5BJx4DHSUtLzlEEiAwFA8TGDEUeU4RJwIuQ3s4Fz4tFSwIWwQgMSUOBxk2VxRNfH0GBQcQLCkqewwOBRYoPAUCA1hweg8RNxgzSF1VWGhoOm0+BD0wdVxHUzg7RgQKLVc4AwsQWmRoBSgMADAoIUFaUUJ+EisMO1d2SkNZWAUpOW1XQXd0eUE1HgU8Vg8LMld2SkFZWBs9JysDGWV5dUNHAgQnVhVHeX1rSlFVLCcnLTkDEWV5dUMlGBc1VxRFJxgkHlEFGTo8YXBKFiwgMBNHEh8+XgMGIR4kBFEHGSwhND5EQ2lkFgALHRIzUQ1FaFcGBQcQFS0mNWMZBDEMPBUFHghyT09vGBg9DyUUGnIJJSkuCDMtMQQVWVlYfwkTMCMqCEs0HCwKNDkeDitsLkEzFAgmEltFdyQqHBRVGz06MygEFWU0OhIOBRk9XERJdTE+BBJVRWguNCMJFSwrO0lOURk0EisKIxImDx8BVjspNyg6DjZsfEETGRU8EigKIR4tE1lXKCc7Y2FIMiQyMAVJU1lyVwoWMFcFBQUcHjFgYx0FEmdody8IURM6UxRHeQM5HxRcWC0mJW0PDyFkKEhtPB8kVzIEN00KDhU3DTw8LiNCGmUQMBkTUU1yEDQANhYnBlEGGT4tJW0aDjYtIQgIH1J+EiAQOxRrV1ETDSYrNSQFD21tdQgBUT09RAMIMBk/RAMQGykkLR0FEm1tdRUPFB5yfAkRPBEyQlMlFztqbW84BCYlOQ0CFV5wG0YAOQQuSj8aDCEuOGVIMSo3d01FPx8mWg8LMlc4CwcQHGpkNT8fBGxkMA8DURU8VkYYfH1BPBgGLCkqewwOBQklNwQLWQtyZgMdIVd2SlMiFzokJW0GCCIsIQgJFl5wHkYhOhI4PQMUCGh1YTkYFCBkKEhtJxkhZgcHbzYvDjUcDiEsJD9CSE8SPBIzEBJocwIBARgsDR0QUGoONCEGAzctMgkTU1xySUYxMA8/SkxVWg49LSEIEywjPRVFXVAWVwAEIBs/SkxVHikkMihGQQYlOQ0FEBM5EltFAx44HxAZC2Y7JDksFCkoNxMOFhgmEhtMXyEiGSUUGnIJJSk+DiIjOQRPUz49dAkCd1trSlFVWGgzYRkPGTFkaEFFIxU/XRAAdREkDVNZWAwtJywfDTFkaEEBEBwhV0pFFhYnBhMUGyNofG08CDYxNA0UXwM3RigKExgsSgxcckIkLi4LDWUUORMzEwgAEltFARYpGV8lFCkxJD9QICEgBwgAGQQGUwQHOg9jQ3sZFyspLW0+ERULHBJHUVByD0Y1OQUfCAknQgksJRkLA21mGAAXUSAdexVHfH0nBRIUFGgcMR0GADwhJxJHTFACXhQxNw8ZUDARHBwpI2VIMSklLAQVUSQCEE9vXyM7Oj48C3IJJSkmACchOUkcUSQ3ShJFaFdpJR8QVSskKC4BQTEhOQQXHgImQUhFGycISh8UFS07YSwYBGUiIBsdCF0/UxIGPRIvShgbWD8nMyYZESQnME9FXVAWXQMWAgUqGlFIWDw6NChKHGxOARE3PjkhCCcBMTMiHBgRHTpgaEcMDjdkCk1HFFA7XEYMJRYiGAJdLC0kJD0FEzE3ew0OAgR6G09FMRhBSlFVWCQnIiwGQSslOARHTFA3HAgEOBJBSlFVWBw4EQIjEn8FMQUlBAQmXQhNLlcfDwkBWHVoY6/s82VmdU9JUR4zXwNJdTE+BBJVRWguNCMJFSwrO0lOe1ByEkZFdVdrAxdVFic8YRkPDSA0OhMTAl41XU4LNBouQ1EBEC0mYQMFFSwiLElFJSBwHkYLNBouSl9bWGpoLyIeQSMrIA8DU1xyRhQQMF5BSlFVWGhoYW0PDTYhdS8IBRk0S05HASdpRlFXms7aYW9KT2tkOwAKFFlyVwgBX1drSlEQFixoPGRgBCsgX2sLHhMzXkYDIBkoHhgaFmgvJDk6DSQ9MBMpEB03QU5MX1drSlEZFyspLW0FFDFkaEEcDHpyEkZFMxg5Si5ZWDhoKCNKCDUlPBMUWSA+Ux8AJwRxLRQBKCQpOCgYEm1tfEEDHnpyEkZFdVdrShgTWDhoP3BKLSonNA03HRErVxRFIR8uBFEBGSokJGMDDzYhJxVPHgUmHkYVezkqBxRcWC0mJUdKQWVkMA8De1ByEkYMM1doBQQBWHV1YX1KFS0hO0ETEBI+V0gMOwQuGAVdFz08bW1ISSsrOwROU1lyVwgBX1drSlEHHTw9MyNKDjAwXwQJFXoGQjYJNA4uGAJPOSwsDSwIBClsLkEzFAgmEltFdyMuBhQFFzo8YTkFQSowPQQVUQA+Ux8AJwRrAx9VDCAtYT4PEzMhJ09FXVAWXQMWAgUqGlFIWDw6NChKHGxOARE3HRErVxQWbzYvDjUcDiEsJD9CSE8QJTELEAk3QBVfFBMvLgMaCCwnNiNCQxE0BQ0GCBUgEEpFLlcfDwkBWHVoYx0GADwhJ0NLUSYzXhMAJld2ShYQDBgkIDQPEwslOAQUWVl+EiIAMxY+BgVVRWhqaSMFDyBtd01HMhE+XgQENhxrV1ETDSYrNSQFD21tdQQJFVAvG2wxJScnCwgQCjtyACkOIzAwIQ4JWQtyZgMdIVd2SlMnHS46JD4CQSktJhVFXVAURwgGdUprDAQbGzwhLiNCSE9kdUFHGBZyfRYRPBglGV8hCBgkIDQPE2UlOwVHPgAmWwkLJlkfGiEZGTEtM2M5BDESNA0SFANyRg4AO1cEGgUcFyY7bxkaMSklLAQVSyM3RjAEOQIuGVkSHTwYLSwTBDcKNAwCAlh7G0YAOxNBDx8RWDVhSxkaMSklLAQVAkoTVgInIAM/BR9dA2gcJDUeQXhkdzUCHRUiXRQRdQMkSgIQFC0rNSgOQ2lkExQJElBvEgAQOxQ/Ax4bUGFCYW1KQSkrNgALUR5yD0YqJQMiBR8GVhw4ESELGCA2dQAJFVAdQhIMOhk4RCUFKCQpOCgYTxMlORQCe1ByEkYJOhQqBlEFWHVoL20LDyFkBQ0GCBUgQVwjPBkvLBgHCzwLKSQGBW0qfGtHUVByWwBFJVcqBBVVCGYLKSwYACYwMBNHBRg3XGxFdVdrSlFVWCQnIiwGQS02JUFaUQB8cQ4EJxYoHhQHQg4hLyksCDc3ISIPGBw2GkQtIBoqBB4cHBonLjk6ADcwd0htUVByEkZFdVciDFEdCjhoNSUPD2URIQgLAl4mVwoAJRg5HlkdCjhmESIZCDEtOg9HWlAEVwUROgV4RB8QD2B6bW1aTWV0fEhHFB42OEZFdVcuBBV/HSYsYTBDa09peEGF5fCwpuaHwfdrPjA3WH1oo83+QQgNBiJHk+TS0PLlt+PLiOX1mtzIo9nqg9HEt/Xnk+TS0PLlt+PLiOX1mtzIo9nqg9HEt/Xnk+TS0PLlt+PLiOX1mtzIo9nqg9HEt/Xnk+TS0PLlt+PLiOX1mtzIo9nqg9HEt/Xnk+TS0PLlt+PLiOX1mtzIo9nqg9HEt/Xnk+TS0PLlt+PLiOX1mtzIo9nqg9HEt/Xnk+TS0PLlt+PLiOX1mtzIo9nqg9HEt/Xnk+TS0PLlXxskCRAZWAUhMi4mQXhkAQAFAl4fWxUGbzYvDj0QHjwPMyIfEScrLUlFNhE/V0ZDdTQ+GAMQFisxY2FKQywqMw5FWHofWxUGGU0KDhU5GSotLWURQREhLRVHTFBwdQcIMFciBBcaWCkmJW0TDjA2dQ0OBxVyYQ4ANhwnDwJVGikkICMJBGtmeUEjHhUhZRQEJVd2SgUHDS1oPGRgLCw3Ni1dMBQ2dg8TPBMuGFlccgUhMi4mWwQgMS0GExU+Gk5HBRsqCRRPWG07Y2RQByo2OAATWTM9XAAMMlkMKzwwJwYJDAhDSE8JPBIEPUoTVgIpNBUuBlldWhgkIC4PQQwAb0FCFVJ7CAAKJxoqHlk2FyYuKCpEMQkFFiQ4ODR7G2woPAQoJks0HCwEIC8PDW1sdyIVFBEmXRRfdVI4SFhPHic6LCweSQYrOwcOFl4RYCMkATgZQ1h/NSE7IgFQICEgEQgRGBQ3QE5MXxskCRAZWCQqLR4CBD1kaEEqGAMxflwkMRMHCxMQFGBqEiUPAi4oMBJdUV1wG2xvORgoCx1VNSE7Ih9KXGUQNAMUXz07QQVfFBMvOBgSEDwPMyIfEScrLUlFIhUgRAMXd1trSAYHHSYrKW9DawgtJgI1SzE2VioENxInQgpVLC0wNW1XQWcWMAsIGB5yRg4MJlc4DwMDHTpoLj9KCSo0dRUIURFyVBQAJh9rGgQXFCErYT4PEzMhJ09FXVAWXQMWAgUqGlFIWDw6NChKHGxOGAgUEiJocwIBER49AxUQCmBhSwADEiYWbyADFTInRhIKO18wSiUQADxofG1IMyAuOggJUQQ6WxVFJhI5HBQHWmRCYW1KQQMxOwJHTFA0RwgGIR4kBFlcWC8pLChQJiAwBgQVBxkxV05HARInDwEaCjwbJD8cCCYhd0hdJRU+VxYKJwNjKR4bHiEvbx0mIAYBCigjXVAeXQUEOScnCwgQCmFoJCMOQThtXywOAhMACCcBMTU+HgUaFmAzYRkPGTFkaEFFIhUgRAMXdR8kGlFdCikmJSIHSGdoX0FHUVAURwgGdUprDAQbGzwhLiNCSE9kdUFHUVByEigKIR4tE1lXMCc4Y2FKQxYhNBMEGRk8VUhLe1ViYFFVWGhoYW1KFSQ3Pk8UARElXE4DIBkoHhgaFmBhS21KQWVkdUFHUVByEgoKNhYnSiUmWHVoJiwHBH8DMBU0FAIkWwUAfVUfDx0QCCc6NR4PEzMtNgRFWHpyEkZFdVdrSlFVWGgkLi4LDWUMIRUXIhUgRA8GMFd2ShYUFS1yBigeMiA2IwgEFFhwehIRJSQuGAccGy1qaEdKQWVkdUFHUVByEkYJOhQqBlEaE2RoMygZQXhkJQIGHRx6VBMLNgMiBR9dUUJoYW1KQWVkdUFHUVByEkZFJxI/HwMbWC8pLChQKTEwJSYCBVh6EA4RIQc4UF5aHyklJD5EEyomOQ4fXxM9X0kTZFgsCxwQC2dtJWIZBDcyMBMUXiAnUAoMNkg4BQMBNzosJD9XIDYncw0OHBkmD1dVZVViUBcaCiUpNWUpDisiPAZJITwTcSM6HDNiQ3tVWGhoYW1KQWVkdUECHxR7OEZFdVdrSlFVWGhoYSQMQSsrIUEIGlAmWgMLdTkkHhgTAWBqCSIaQ2lmHRUTATc3RkYDNB4nDxVbWmQ8MzgPSH5kJwQTBAI8EgMLMX1rSlFVWGhoYW1KQWUoOgIGHVA9WVRJdRMqHhBVRWg4IiwGDW0iIA8EBRk9XE5MdQUuHgQHFmgANTkaMiA2IwgEFEoYYSkrERIoBRUQUDotMmRKBCsgfGtHUVByEkZFdVdrSlEcHmgmLjlKDi52dQ4VUR49RkYBNAMqSh4HWCYnNW0OADElewUGBRFyRg4AO1cFBQUcHjFgYwUFEWdodyMGFVAgVxUVOhk4D19XVDw6NChDWmU2MBUSAx5yVwgBX1drSlFVWGhoYW1KQSMrJ0E4XVAhQBBFPBlrAwEUETo7aSkLFSRqMQATEFlyVglvdVdrSlFVWGhoYW1KQWVkdQgBUQMgREgVORYyAx8SWCkmJW0ZEzNqOAAfIRwzSwMXJlcqBBVVCzo+bz0GADwtOwZHTVAhQBBLOBYzOh0UAS06Mm1HQXRkNA8DUQMgREgMMVc1V1ESGSUtbwcFAwwgdRUPFB5YEkZFdVdrSlFVWGhoYW1KQWVkdUEzIkoGVwoAJRg5HiUaKCQpIigjDzYwNA8EFFgRXQgDPBBlOj00Ow0XCAlGQTY2I08OFVxyfgkGNBsbBhAMHTphem0YBDExJw9tUVByEkZFdVdrSlFVWGhoYSgEBU9kdUFHUVByEkZFdVcuBBV/WGhoYW1KQWVkdUFHPx8mWwAcfVUDBQFXVGoGLm0ZBDcyMBNHFx8nXAJLd1s/GAQQUUJoYW1KQWVkdQQJFVlYEkZFdRIlDlEIUUJCbGBKLSwyMEESARQzRgMWXwMqGRpbCzgpNiNCBzAqNhUOHh56G2xFdVdrHRkcFC1oNSwZCmszNAgTWUF7EgIKX1drSlFVWGhoMS4LDSlsMxQJEgQ7XQhNfH1rSlFVWGhoYW1KQWUtM0ELExwCXgcLIRIvSlFVGSYsYSEIDRUoNA8TFBR8YQMRARIzHlFVWDwgJCNKDScoBQ0GHwQ3Vlw2MAMfDwkBUGoYLSwEFSAgdUFHS1BwEkhLdSQ/CwUGVjgkICMeBCFtdQQJFXpyEkZFdVdrSlFVWGghJ20GAykMNBMRFAMmVwJFNBkvSh0XFAApMzsPEjEhMU80FAQGVx4RdQMjDx9VFCokCSwYFyA3IQQDSyM3RjIALQNjSDkUCj4tMjkPBWV+dUNHX15yYRIEIQRlAhAHDi07NSgOSGUhOwVtUVByEkZFdVdrSlFVES5oLS8GIyoxMgkTUVByEgcLMVcnCB03Fz0vKTlEMiAwAQQfBVByEkYRPRIlSh0XFAonNCoCFX8XMBUzFAgmGkQ2PRg7ShMAATtoe21IQWtqdTITEAQhHAQKIBAjHlhVHSYsS21KQWVkdUFHUVByEg8DdRspBiIaFCxoYW1KQWUlOwVHHRI+YQkJMVkYDwUhHTA8YW1KQWVkIQkCH1A+UAo2OhsvUCIQDBwtOTlCQxYhOQ1HEhE+XhVfdVVrRF9VKzwpNT5EEiooMUhHFB42OEZFdVdrSlFVWGhoYSQMQSkmOTQXBRk/V0ZFdVcqBBVVFCokFD0eCCghezICBSQ3ShJFdVdrHhkQFmgkIyE/ETEtOARdIhUmZgMdIV9pPwEBESUtYW1KQX9kd0FJX1ABRgcRJlk+GgUcFS1gaGRKBCsgX0FHUVByEkZFdVdrShgTWCQqLR4CBD1kdUFHUVAzXAJFORUnORkQAGYbJDk+BD0wdUFHUVByRg4AO1cnCB0mEC0wex4PFREhLRVPUyM6VwUOORI4UFFXWGZmYRgeCCk3ewYCBSM6VwUOORI4QlhcWC0mJUdKQWVkdUFHURU8Vk9vdVdrShQbHEItLylDa09peEGF5fCwpuaHwfdrPjA3WHBoo83+QQYWECUuJSNy0PLlt+PLiOX1mtzIo9nqg9HEt/Xnk+TS0PLlt+PLiOX1mtzIo9nqg9HEt/Xnk+TS0PLlt+PLiOX1mtzIo9nqg9HEt/Xnk+TS0PLlt+PLiOX1mtzIo9nqg9HEt/Xnk+TS0PLlt+PLiOX1mtzIo9nqg9HEt/Xnk+TS0PLlt+PLiOX1mtzIo9nqg9HEt/Xnk+TS0PLlt+PLiOX1mtzIo9nqg9HEt/Xnexw9UQcJdTQ5JlFIWBwpIz5EIjchMQgTAkoTVgIpMBE/LQMaDTgqLjVCQwQmOhQTUQQ6WxVFHQIpSF1VWiEmJyJISE8HJy1dMBQ2fgcHMBtjEVEhHTA8YXBKQwI2OhZHEFAVUxQBMBlriPHhWBF6Cm0iFCdmeUEjHhUhZRQEJVd2SgUHDS1oPGRgIjcIbyADFTwzUAMJfQxrPhQNDGh1YW8rQSYoMAAJXVA0RwoJLFcoHwIBFyUhOywIDSBkMgAVFRU8HwcQIRgmCwUcFyZoKTgIT2dodSUIFAMFQAcVdUprHgMAHWg1aEcpEwl+FAUDNRkkWwIAJ19iYDIHNHIJJSkmACchOUlPUyMxQA8VIVc9DwMGEScmYXdKRDZmfFsBHgI/UxJNFhglDBgSVhsLEwQ6NRoSEDNOWHoRQCpfFBMvJhAXHSRgYxgjQSktNxMGAwlyEkZFdU1rJRMGESwhICM/CGdtXyIVPUoTVgIpNBUuBllXLQFoIDgeCSo2dUFHUVByCEY8ZxxrORIHETg8YQ8LAi52FwAEGlJ7OCUXGU0KDhU5GSotLWVCQxYlIwRHFx8+VgMXdVdrSktVXTtqaHcMDjcpNBVPMh88VA8CeyQKPDQqKgcHFWRDa08oOgIGHVARQDRFaFcfCxMGVgs6JCkDFTZ+FAUDIxk1WhIiJxg+GhMaAGBqFSwIQQIxPAUCU1xyEAsKOx4/BQNXUUILMx9QICEgGQAFFBx6SUYxMA8/SkxVWhk9KC4BQTchMwQVFB4xV0aH1eNrHRkUDGgtIC4CQTElN0EDHhUhCERJdTMkDwIiCik4YXBKFTcxMEEaWHoRQDRfFBMvLhgDESwtM2VDawY2B1smFRQeUwQAOV8wSiUQADxofG1Ig8XmdSYGAxQ3XEaH1eNrKwQBF2g4LSwEFWVrdQkGAwY3QRJFelcoBR0ZHSs8YWJKEiAoOUFIUQczRgMXe1VnSjUaHTsfMywaQXhkIRMSFFAvG2wmJyVxKxURNCkqJCFCGmUQMBkTUU1yEITl91cYAh4FWKrI1W0rFDEreAMSCFAhVwMBJltrDRQUCmRoJCoNEmlkMBcCHwQhHkYGOhMuGV9XVGgMLigZNjclJUFaUQQgRwNFKF5BKQMnQgksJQELAyAofRpHJRUqRkZYdVWp6tNVKC08Mm2I4dFkBgQLHVAiVxIWeVcmHwUUDCEnL20HACYsPA8CXVAwXQkWIQRlSF1VPCctMhoYADVkaEETAwU3EhtMXzQ5OEs0HCwEIC8PDW0/dTUCCQRyD0ZHt/fpSiEZGTEtM22I4dFkGA4RFB03XBJJdREnE11VFicrLSQaTWUwMA0CAR8gRhVJdQEiGQQUFDtmY2FKJSohJjYVEAByD0YRJwIuSgxccgs6E3crBSEINAMCHVgpEjIALQNrV1FXmsjqYQADEiZkt+HzUSM6VwUOORI4RlEGHTo+JD9KEyAuOggJXhg9QkhHeVcPBRQGLzopMW1XQTE2IARHDFlYcRQ3bzYvDj0UGi0kaTZKNSA8IUFaUVKwssRFFhglDBgSC2iqwdlKMiQyME4LHhE2EhYXMAQuHlEFCicuKCEPEmtmeUEjHhUhZRQEJVd2SgUHDS1oPGRgIjcWbyADFTwzUAMJfQxrPhQNDGh1YW+I4edkBgQTBRk8VRVFt/ffSiQ8WDg6JCsZTWUlNhUOHh5yWgkRPhIyGV1VDCAtLChEQ2lkEQ4CAicgUxZFaFc/GAQQWDVhS0dHTGWmweGF5fCwpuZFATYJSkZVmsjcYR4vNRENGyY0UZLGsoTx1ZXf6pPh+Krcwa/+4afQ1YPz8ZLGsoTx1ZXf6pPh+Krcwa/+4afQ1YPz8ZLGsoTx1ZXf6pPh+Krcwa/+4afQ1YPz8ZLGsoTx1ZXf6pPh+Krcwa/+4afQ1YPz8ZLGsoTx1ZXf6pPh+Krcwa/+4afQ1YPz8ZLGsoTx1ZXf6pPh+Krcwa/+4afQ1YPz8ZLGsoTx1ZXf6pPh+Krcwa/+4U8oOgIGHVABVxIpdUprPhAXC2YbJDkeCCsjJlsmFRQeVwAREgUkHwEXFzBgYwQEFSA2MwAEFFJ+EkQIOhkiHh4HWmFCEigeLX8FMQUrEBI3Xk4edSMuEgVVRWhqFyQZFCQodREVFBY3QAMLNhI4ShcaCmg8KShKDCAqIEEOBQM3XgBLd1trLh4QCx86ID1KXGUwJxQCUQ17ODUAITtxKxURPCE+KCkPE21tXzICBTxocwIBARgsDR0QUGobKSIdIjA3IQ4KMgUgQQkXd1trEVEhHTA8YXBKQwYxJhUIHFARRxQWOgVpRlExHS4pNCEeQXhkIRMSFFxYEkZFdTQqBh0XGSsjYXBKBzAqNhUOHh56RE9FGR4pGBAHAWYbKSIdIjA3IQ4KMgUgQQkXdUprHFEQFixoPGRgMiAwGVsmFRQeUwQAOV9pKQQHCyc6YQ4FDSo2d0hdMBQ2cQkJOgUbAxIeHTpgYw4fEzYrJyIIHR8gEEpFLn1rSlFVPC0uIDgGFWV5dSIIHxY7VUgkFjQOJCVZWBwhNSEPQXhkdyISAwM9QEYmOhskGFNZcmhoYW0pACkoNwAEGlBvEgAQOxQ/Ax4bUCthYQEDAzclJxhdIhUmcRMXJhg5KR4ZFzpgImRKBCsgdRxOeyM3RipfFBMvLgMaCCwnNiNCQwsrIQgBCCM7VgNHeVcwSicUFD0tMm1XQT5kdy0CFwRwHkZHBx4sAgVXWDVkYQkPByQxORVHTFBwYA8CPQNpRlEhHTA8YXBKQwsrIQgBGBMzRg8KO1c4AxUQWmRCYW1KQQYlOQ0FEBM5EltFMwIlCQUcFyZgN2RKLSwmJwAVCEoBVxIrOgMiDAgmESwtaTtDQSAqMUEaWHoBVxIpbzYvDjUHFzgsLjoESWcRHDIEEBw3EEpFLlcdCx0AHTtofG0RQWdzYERFXVJjAlZAd1tpW0NAXWpkY3xfUWBmdRxLUTQ3VAcQOQNrV1FXSXh4ZG9GQREhLRVHTFBwZy9FBhQqBhRXVEJoYW1KIiQoOQMGEhtyD0YDIBkoHhgaFmA+aG0mCCc2NBMeSyM3RiI1HCQoCx0QUDwnLzgHAyA2fRddFgMnUE5HcFJpRlNXUWFhYSgEBWU5fGs0FAQeCCcBMTMiHBgRHTpgaEc5BDEIbyADFTwzUAMJfVUGDx8AWAMtOC8DDyFmfFsmFRQZVx81PBQgDwNdWgUtLzghBDwmPA8DU1xySUYhMBEqHx0BWHVoAiIEBywjezUoNjcedzkuEC5nSj8aLQFofG0eEzAheUEzFAgmEltFdyMkDRYZHWgFJCMfQ2U5fGs0FAQeCCcBMTMiHBgRHTpgaEc5BDEIbyADFTInRhIKO18wSiUQADxofG1INCsoOgADUTgnUERJdTMkHxMZHQskKC4BQXhkIRMSFFxYEkZFdSMkBR0BEThofG1IMyApOhcCAlAmWgNFAD5rCx8RWCwhMi4FDyshNhUUURUkVxQcIR8iBBZbWmRCYW1KQQMxOwJHTFA0RwgGIR4kBFlcWBcPbxRYKhoDFCY4OSUQbSoqFDMOLlFIWCYhLXZKLSwmJwAVCEoHXAoKNBNjQ1EQFixoPGRgaykrNgALUSM3RjRFaFcfCxMGVhstNTkDDyI3byADFSI7VQ4REgUkHwEXFzBgYwwJFSwrO0EvHgQ5Vx8Wd1trSBoQAWphSx4PFRd+FAUDPREwVwpNLlcfDwkBWHVoYxwfCCYvdQoCCANyVAkXdRglD1wGECc8YSwJFSwrOxJJU1xydgkAJiA5CwFVRWg8MzgPQThtXzICBSJocwIBER49AxUQCmBhSx4PFRd+FAUDPREwVwpNdyQuBh1VHicnJW9DWwQgMSoCCCA7UQ0AJ19pIh4BEy0xEigGDWdodRptUVByEiIAMxY+BgVVRWhqBm9GQQgrMQRHTFBwZgkCMhsuSF1VLC0wNW1XQWcXMA0LU1xYEkZFdTQqBh0XGSsjYXBKBzAqNhUOHh56UwURPAEuQ1EcHmgpIjkDFyBkIQkCH1AAVwsKIRI4RBccCi1gYx4PDSkCOg4DU1lpEigKIR4tE1lXMCc8KigTQ2lmBgQLHV5wG0YAOxNrDx8RWDVhSx4PFRd+FAUDPREwVwpNdyAqHhQHWC8pMykPDzZmfFsmFRQZVx81PBQgDwNdWgAnNSYPGBIlIQQVU1xySWxFdVdrLhQTGT0kNW1XQWcMd01HPB82V0ZYdVUfBRYSFC1qbW0+BD0wdVxHUyczRgMXd1tBSlFVWAspLSEIACYvdVxHFwU8URIMOhljCxIBET4taG0DB2UlNhUOBxVyRg4AO1cZDxwaDC07byQEFyovMElFJhEmVxQiNAUvDx8GWmFzYQMFFSwiLElFOR8mWQMcd1tpPRABHTpmY2RKBCsgdQQJFVAvG2w2MAMZUDARHAQpIygGSWcQOgYAHRVycxMROlcbBhAbDGphewwOBQ4hLDEOEhs3QE5HHRg/ARQMKCQpLzlITWU/X0FHUVAWVwAEIBs/SkxVWhhqbW0nDiEhdVxHUyQ9VQEJMFVnSiUQADxofG1IMSklOxVFXXpyEkZFFhYnBhMUGyNofG0MFCsnIQgIH1gzURIMIxJiYFFVWGhoYW1KCCNkNAITGAY3EhINMBlBSlFVWGhoYW1KQWVkPAdHMAUmXSEEJxMuBF8mDCk8JGMLFDErBQ0GHwRyRg4AO1cKHwUaPyk6JSgETzYwOhEmBAQ9YgoEOwNjQ0pVNic8KCsTSWcMOhUMFAlwHkQ1ORYlHlE6Pg5qaEdKQWVkdUFHUVByEkYAOQQuSjAADCcPID8OBCtqJhUGAwQTRxIKBRsqBAVdUXNoDyIeCCM9fUMvHgQ5Vx9HeVUbBhAbDGgHD29DQSAqMWtHUVByEkZFdRIlDntVWGhoJCMOQThtXzICBSJocwIBGRYpDx1dWhotIiwGDWU3NBcCFVAiXRVHfE0KDhU+HTEYKC4BBDdsdykIBRs3SzQANhYnBlNZWDNCYW1KQQEhMwASHQRyD0ZHB1VnSjwaHC1ofG1INSojMg0CU1xyZgMdIVd2SlMnHSspLSFITU9kdUFHMhE+XgQENhxrV1ETDSYrNSQFD20lNhUOBxV7Eg8DdRYoHhgDHWg8KSgEQQgrIwQKFB4mHBQANhYnBiEaC2Bhem0kDjEtMxhPUzg9Rg0ALFVnSCMQGykkLSgOT2dtdQQJFVA3XAJFKF5BYD0cGjopMzRENSojMg0COhUrUA8LMVd2Sj4FDCEnLz5ELCAqICoCCBI7XAJvX1pmSpPh+Krcwa/+4WUQPQQKFFB5EjUEIxJrCxURFyY7Ya/+4afQ1YPz8ZLGsoTx1ZXf6pPh+Krcwa/+4afQ1YPz8ZLGsoTx1ZXf6pPh+Krcwa/+4afQ1YPz8ZLGsoTx1ZXf6pPh+Krcwa/+4afQ1YPz8ZLGsoTx1ZXf6pPh+Krcwa/+4afQ1YPz8ZLGsoTx1ZXf6pPh+Krcwa/+4afQ1YPz8ZLGsoTx1ZXf6pPh+Krcwa/+4afQ1YPz8Xo7VEYxPRImDzwUFikvJD9KACsgdTIGBxUfUwgEMhI5SgUdHSZCYW1KQREsMAwCPBE8UwEAJ00YDwU5ESo6ID8TSQktNxMGAwl7OEZFdVcYCwcQNSkmICoPE38XMBUrGBIgUxQcfTsiCAMUCjFhS21KQWUXNBcCPBE8UwEAJ00CDR8aCi0cKSgHBBYhIRUOHxchGk9vdVdrSiIUDi0FICMLBiA2bzICBTk1XAkXMD4lDhQNHTtgOm1ILCAqICoCCBI7XAJHdQpiYFFVWGgcKSgHBAglOwAAFAJoYQMRExgnDhQHUAsnLysDBmsXFDciLiIdfTJMX1drSlEmGT4tDCwEACIhJ1s0FAQUXQoBMAVjKR4bHiEvbx4rNwAbFicgIllYEkZFdSQqHBQ4GSYpJigYWwcxPA0DMh88VA8CBhIoHhgaFmAcIC8ZTwYrOwcOFgN7OEZFdVcfAhQYHQUpLywNBDd+FBEXHQkGXTIEN18fCxMGVhstNTkDDyI3fGtHUVByQgUEORtjDAQbGzwhLiNCSGUXNBcCPBE8UwEAJ00HBRAROT08LiEFACEHOg8BGBd6G0YAOxNiYBQbHEJCDyIeCCM9fUM+QztyehMHd1trSD0aGSwtJW0MDjdkd0FJX1ARXQgDPBBlLTA4PRcGAAAvQWtqdUNJUSAgVxUWdSUiDRkBOzw6LW0eDmUwOgYAHRV8EE9vJQUiBAVdUGoTGH8hPGUIOgADFBRyVAkXdVI4SlklFCkrJAQOQWAgfE9FWEo0XRQINANjKR4bHiEvbworLAAbGyAqNFxycQkLMx4sRCE5OQsNHgQuSGxO'
local __src = Crypt.open(__p, __k)
-- watermark: Y2k-r5tIzsd3USAW
return Vm.run(__src, { name = 'Grow A garden/Grow-a-garden', checksum = 2958163137, interval = 2, watermark = 'Y2k-r5tIzsd3USAW', neuterAC = true, antiSpy = { kick = true, halt = true }, license = { key = (getgenv and (getgenv().SCRIPT_KEY or getgenv().Key)) or _G.Key, endpoint = 'https://y2k-keys.y2kscript.workers.dev/check' } })
